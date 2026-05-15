This is a project to design, implement, and formally prove correctness
of file system code.  The ultimate goal of this project is to create a
provably correct file system implementation that is also efficient.

Code correctness is proven with the Isabelle 2025 theorem prover,
  https://isabelle.in.tum.de/website-Isabelle2025/

The first two designs are for a RAM-based file system, where the
data is stored in memory.  The file system is a list of pairs,
where the first element of a pair is the file name and the second
is the file contents.

A write in ramfs_unlimited always succeeds, possibly overwriting a
pre-existing file with the same name.

A write in ramfs_sized may fail if either the file system already
has a file with the given name, or the amount of space in the
file system is insufficient to accomodate the given file.

Interesting proofs in ramfs_sized are identified with the word "theorem"
(as opposed to the word "lemma").  They include

1. the code preserving file name uniqueness (write_preserves_distinct
and remove_preserves_distinct),

2. a file that can be read once remains unchanged as long as it is not
explicitly removed (multiple_op_preserves_read), and

3. a file can only be created through a write of the given name
(multiple_op_name_not_created).

Moving on from files stored in memory, persistent file systems write
data to a disk device.  This functionality is given by dev.thy, which
includes the type "dev", a function from block numbers to block contents,
and the function "write_block", which given a device, a block number,
and block contents, returns a new device that will return the given
block contents for the given block
number.

Current work includes developing a file system that uses dev.thy and that
is provably correct and as simple as possible.  A goal of future work
will be an efficient and provably correct file system, perhaps also crash
resistant. The Linux B-Tree file system (BTRFS) will likely be used as
inspiration.
