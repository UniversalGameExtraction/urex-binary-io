//! A crate that implements endianed BinaryReaders for use in urex.
//!
//! This crate provides the [`BinaryRead`] and [`BinaryWrite`] traits and three implementations of them each.
//!
//! The [`BinaryRead`] and [`BinaryWrite`] traits aren't implemented for [`std::io::Read`] and [`std::io::Write`] respectively, because
//! they are not endian aware. Instead, they are implemented for the three endian aware structs that either set the endianness or make it variable.
//!
//! The implementations are namely:
//! - [`BinaryReaderVE`], [`BinaryReaderLE`], [`BinaryReaderBE`]
//! - [`BinaryWriterVE`], [`BinaryWriterLE`], [`BinaryWriterBE`].
//!
//! The `VE` stands for variable endian, the `LE` stands for little-endian, and the `BE` stands for big-endian.
//!
//! The [`BinaryReaderVE`] and [`BinaryWriterVE`] structs are flexible, allowing you to set and change the endianness at runtime.
//! The endianness can be set by setting the `endian` field, which is of type [`Endian`].<br>
//! The [`BinaryReaderLE`] and [`BinaryWriterLE`] structs are restrictive, as they only allow you to read/write little-endian data.<br>
//! The [`BinaryReaderBE`] and [`BinaryWriterBE`] structs are restrictive, as they only allow you to read/write big-endian data.

mod reader;
mod writer;

pub use reader::{BinaryRead, BinaryReadAlign, BinaryReaderBE, BinaryReaderLE, BinaryReaderVE};
pub use writer::{BinaryWrite, BinaryWriteAlign, BinaryWriterBE, BinaryWriterLE, BinaryWriterVE};

/// A simple enum to represent the endianness of the data.<br>
/// For use with the [`BinaryReaderVE`] and [`BinaryReaderBE`] structs.
pub enum Endian {
    Little,
    Big,
}
