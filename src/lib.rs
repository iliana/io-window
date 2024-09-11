//! This library contains [`IoWindow`], an I/O adapter for a stream of bytes
//! that limits operations within a byte range.
//!
//! An `IoWindow` is conceptually similar to a mutable slice, applied to
//! a reader or writer. Given a byte range `start..end`, position 0 of the
//! `IoWindow` is position `start` of the underlying object; the end position of
//! the `IoWindow` is position `start + end` of the underlying object; and the
//! length of the `IoWindow` is `end - start`.
//!
//! ```
//! # use std::io::prelude::*;
//! use io_window::IoWindow;
//!
//! # fn main() -> std::io::Result<()> {
//! let stream = std::io::Cursor::new([0; 8]);
//! let mut window = IoWindow::new(stream, 2..6)?;
//! assert_eq!(window.write(&[42; 16])?, 4);
//! assert_eq!(
//!     window.into_inner().into_inner(),
//!     [0, 0, 42, 42, 42, 42, 0, 0]
//! );
//! # Ok(())
//! # }
//! ```
//!
//! One use of this library is operating within a partition of a disk image.
//! For instance, if you have a filesystem implementation that uses a
//! `Read + Write + Seek` object, you can use `IoWindow` to avoid needing to
//! copy a disk image's partition into memory or another file, or reaching for a
//! memory-mapped buffer.
//!
//! ```
//! # use std::fs::File;
//! # use io_window::IoWindow;
//! const MEBIBYTE: u64 = 1024 * 1024;
//!
//! # fn main() -> std::io::Result<()> {
//! # let disk = "/dev/null";
//! let file = File::open(disk)?;
//! let mut partition = IoWindow::new(file, MEBIBYTE..(64 * MEBIBYTE))?;
//! # Ok(())
//! # }
//! ```
//!
//! It's also possible to provide a range with an unbounded end. If you were
//! working with a file with a header that you needed the ability to modify and
//! append to, you could use a range like `1024..` to create an `IoWindow` from
//! position 1024 to the end of the file.

#![warn(clippy::pedantic)]

use std::io::{Read, Seek, SeekFrom, Write};
use std::ops::{Bound, RangeBounds};

/// Seekable I/O adapter that limits operations to a byte range.
///
/// For more, see the [crate documentation](self).
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct IoWindow<T: Seek> {
    inner: T,
    start: u64,
    end: Option<u64>,
}

impl<T: Seek> IoWindow<T> {
    /// Adapts an object to limit I/O operations within a byte range.
    ///
    /// If the current position is earlier than the start of the range, the
    /// object is seeked to that start.
    ///
    /// A range with an unbounded start (for example, `..1024`) is treated as
    /// starting at `0`.
    ///
    /// A range with an unbounded end (for example, `1024..`) means
    /// the window ends at the end of the stream. Writing past the end
    /// of the window is supported if the underlying object can grow
    /// its length (some examples include [`File`](std::fs::File) and
    /// [`Cursor<Vec<u8>>`][std::io::Cursor]).
    ///
    /// # Errors
    ///
    /// Returns an error if determining the current position or seeking fails.
    pub fn new(mut inner: T, range: impl RangeBounds<u64>) -> std::io::Result<IoWindow<T>> {
        let start = match range.start_bound() {
            Bound::Included(pos) => *pos,
            Bound::Excluded(pos) => pos.checked_add(1).ok_or(BadRange)?,
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Included(pos) => Some(pos.checked_add(1).ok_or(BadRange)?),
            Bound::Excluded(pos) => Some(*pos),
            Bound::Unbounded => None,
        };
        if inner.stream_position()? < start {
            inner.seek(SeekFrom::Start(start))?;
        }
        Ok(IoWindow { inner, start, end })
    }

    /// Consumes this adapter, returning the underlying object.
    pub fn into_inner(self) -> T {
        self.inner
    }

    /// Gets a reference to the underlying object.
    pub fn get_ref(&self) -> &T {
        &self.inner
    }

    /// Gets a mutable reference to the underlying object.
    ///
    /// It is a logic error to seek the object earlier than the start of the
    /// window. If you're not absolutely certain that code using this mutable
    /// reference upholds this requirement, call [`Seek::rewind`] on this
    /// adapter immediately after using the mutable reference.
    pub fn get_mut(&mut self) -> &mut T {
        &mut self.inner
    }

    /// Given a buffer of size `len`, return either `len` or the number of bytes
    /// remaining in our window if it's smaller.
    fn reduce_buf_len(&mut self, len: usize) -> std::io::Result<usize> {
        Ok(if let Some(end) = self.end {
            if let Some(remaining) = end.checked_sub(self.inner.stream_position()?) {
                // `usize::try_from` only fails here if `remaining` is larger
                // than `usize::MAX`; if that's the case, it must be larger
                // then `len`.
                match usize::try_from(remaining) {
                    Ok(remaining) => len.min(remaining),
                    Err(_) => len,
                }
            } else {
                // If the position is beyond the end, there are no bytes
                // remaining.
                0
            }
        } else {
            len
        })
    }
}

impl<T: Read + Seek> Read for IoWindow<T> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let len = self.reduce_buf_len(buf.len())?;
        self.inner.read(&mut buf[..len])
    }
}

impl<T: Write + Seek> Write for IoWindow<T> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let len = self.reduce_buf_len(buf.len())?;
        self.inner.write(&buf[..len])
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.inner.flush()
    }
}

impl<T: Seek> Seek for IoWindow<T> {
    fn seek(&mut self, pos: SeekFrom) -> std::io::Result<u64> {
        let adjusted = match pos {
            SeekFrom::Start(pos) => SeekFrom::Start(self.start.checked_add(pos).ok_or(BadSeek)?),
            SeekFrom::End(pos) => {
                if let Some(end) = self.end {
                    SeekFrom::Start(checked_add_signed(end, pos).ok_or(BadSeek)?)
                } else {
                    SeekFrom::End(pos)
                }
            }
            SeekFrom::Current(0) => SeekFrom::Current(0),
            SeekFrom::Current(pos) => SeekFrom::Start(
                checked_add_signed(self.inner.stream_position()?, pos).ok_or(BadSeek)?,
            ),
        };
        if let SeekFrom::Start(start) = adjusted {
            if start < self.start {
                Err(BadSeek)?;
            }
        }
        Ok(self.inner.seek(adjusted)? - self.start)
    }
}

#[inline]
fn checked_add_signed(lhs: u64, rhs: i64) -> Option<u64> {
    if rhs.is_negative() {
        lhs.checked_sub(rhs.unsigned_abs())
    } else {
        lhs.checked_add(rhs.unsigned_abs())
    }
}

macro_rules! err_shortcut {
    ($ident:ident, $str:literal) => {
        struct $ident;

        impl From<$ident> for std::io::Error {
            #[inline]
            fn from(_: $ident) -> std::io::Error {
                std::io::Error::new(std::io::ErrorKind::InvalidInput, $str)
            }
        }
    };
}
err_shortcut!(BadRange, "overflowing range bound");
err_shortcut!(
    BadSeek,
    "invalid seek to a negative or overflowing position"
);

#[cfg(test)]
mod tests {
    use std::io::{Cursor, Read, Seek, SeekFrom, Write};

    use super::IoWindow;

    #[test]
    fn range() -> std::io::Result<()> {
        let v = Cursor::new(vec![0; 512]);
        let mut window = IoWindow::new(v, 128..256)?;
        assert_eq!(window.stream_position()?, 0);
        assert_eq!(window.get_mut().stream_position()?, 128);

        macro_rules! t {
            ($seekfrom:expr, $windowpos:expr, $innerpos:expr) => {{
                assert_eq!(window.seek($seekfrom)?, $windowpos);
                assert_eq!(window.stream_position()?, $windowpos);
                assert_eq!(window.inner.stream_position()?, $innerpos);
            }};
        }

        // seeks within 128..256 work as expected)
        t!(SeekFrom::Start(0), 0, 128);
        t!(SeekFrom::Start(32), 32, 160);
        t!(SeekFrom::End(0), 128, 256);
        t!(SeekFrom::End(-32), 96, 224);
        t!(SeekFrom::Current(-32), 64, 192);

        // reads/writes work as expected
        let mut buf = [0; 16];
        t!(SeekFrom::Start(0), 0, 128);
        assert_eq!(window.write(b"meow meow meow")?, 14);
        t!(SeekFrom::Current(0), 14, 142);
        assert!(window
            .inner
            .get_ref()
            .iter()
            .eq([0; 128].iter().chain(b"meow meow meow").chain(&[0; 370])));
        t!(SeekFrom::Current(-4), 10, 138);
        assert_eq!(window.read(&mut buf[..4])?, 4);
        assert_eq!(&buf[..4], b"meow");

        // reads/writes at the end of the range don't go out of the range
        t!(SeekFrom::End(-4), 124, 252);
        assert_eq!(window.write(b"meow meow meow")?, 4);
        t!(SeekFrom::Current(0), 128, 256);
        assert_eq!(&window.inner.get_ref()[256..], &[0; 256]);
        t!(SeekFrom::End(-8), 120, 248);
        assert_eq!(window.read(&mut buf[..])?, 8);
        t!(SeekFrom::Current(0), 128, 256);
        assert_eq!(&buf[..8], b"\0\0\0\0meow");

        // seeking to a negative position relative to `start` should fail, and
        // the position should not change
        assert!(window.seek(SeekFrom::Current(-160)).is_err());
        t!(SeekFrom::Current(0), 128, 256);
        assert!(window.seek(SeekFrom::End(-160)).is_err());
        t!(SeekFrom::Current(0), 128, 256);

        // like Cursor, seeking beyond the end of the stream should work, but
        // both reads and writes return Ok(0)
        t!(SeekFrom::End(64), 192, 320);
        assert_eq!(window.read(&mut [0; 64])?, 0);
        t!(SeekFrom::Current(0), 192, 320);
        assert_eq!(window.write(&[0; 64])?, 0);
        t!(SeekFrom::Current(0), 192, 320);

        let v = window.into_inner().into_inner();
        assert_eq!(v.len(), 512);
        assert_eq!(v.capacity(), 512);

        Ok(())
    }

    #[test]
    fn range_unbounded() -> std::io::Result<()> {
        let v = Cursor::new(Vec::new());
        let mut window = IoWindow::new(v, 128..)?;

        assert_eq!(window.inner.stream_position()?, 128);
        assert_eq!(window.inner.get_ref().len(), 0);
        window.write_all(b"meow")?;
        assert_eq!(window.inner.get_ref().len(), 132);

        window.seek(SeekFrom::Start(0))?;
        let mut buf = [0; 8];
        assert_eq!(window.read(&mut buf[..])?, 4);
        assert_eq!(&buf[..4], b"meow");

        Ok(())
    }

    #[test]
    fn zero_range() -> std::io::Result<()> {
        let mut window = IoWindow::new(Cursor::new(Vec::new()), 0..0)?;
        assert_eq!(window.write(&[0; 4])?, 0);
        assert_eq!(window.read(&mut [0; 4])?, 0);
        Ok(())
    }

    #[test]
    fn wrapped() -> std::io::Result<()> {
        let inner = IoWindow::new(Cursor::new([0; 512]), 128..256)?;
        let mut window = IoWindow::new(inner, 32..64)?;
        assert_eq!(window.write(&[42; 128])?, 32);
        assert_eq!(window.stream_position()?, 32);
        let mut inner = window.into_inner();
        assert_eq!(inner.stream_position()?, 64);
        let mut cursor = inner.into_inner();
        assert_eq!(cursor.stream_position()?, 192);
        assert!(cursor
            .get_ref()
            .iter()
            .eq([0; 160].iter().chain(&[42; 32]).chain(&[0; 320])));
        Ok(())
    }
}
