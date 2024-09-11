# io-window

This library contains [`IoWindow`], an I/O adapter for a stream of bytes
that limits operations within a byte range.

An `IoWindow` is conceptually similar to a mutable slice, applied to
a reader or writer. Given a byte range `start..end`, position 0 of the
`IoWindow` is position `start` of the underlying object; the end position of
the `IoWindow` is position `start + end` of the underlying object; and the
length of the `IoWindow` is `end - start`.

```rust
use io_window::IoWindow;

let stream = std::io::Cursor::new([0; 8]);
let mut window = IoWindow::new(stream, 2..6)?;
assert_eq!(window.write(&[42; 16])?, 4);
assert_eq!(
    window.into_inner().into_inner(),
    [0, 0, 42, 42, 42, 42, 0, 0]
);
```

One use of this library is operating within a partition of a disk image.
For instance, if you have a filesystem implementation that uses a
`Read + Write + Seek` object, you can use `IoWindow` to avoid needing to
copy a disk image's partition into memory or another file, or reaching for a
memory-mapped buffer.

```rust
const MEBIBYTE: u64 = 1024 * 1024;

let file = File::open(disk)?;
let mut partition = IoWindow::new(file, MEBIBYTE..(64 * MEBIBYTE))?;
```

It's also possible to provide a range with an unbounded end. If you were
working with a file with a header that you needed the ability to modify and
append to, you could use a range like `1024..` to create an `IoWindow` from
position 1024 to the end of the file.

License: MPL-2.0
