//! A normal task, built on the crate's grain: streaming log analysis.
//!
//! We read lines of an access log, parse each into a record, and compute
//! several statistics in a SINGLE PASS — without collecting the parsed
//! records into an intermediate `Vec`. The three spines each do their job:
//!
//! * `base`  — pipeline morphisms parse and classify each line (pure,
//!             zero-sized, fused at compile time).
//! * `machines` — Moore machines accumulate running statistics; `DuplicateToTransducer`
//!             runs several at once over the same stream; `Postmap`
//!             finalizes their readouts.
//! * the seam — `Driven` turns the machine into an `Absorb` sink so a
//!             `Visit` source can feed it; one pass, many answers.
//!
//! The point: the "parse → classify → accumulate several stats at once"
//! shape is exactly product/coproduct/fanout, and the crate lets us write
//! it as composition with no allocation between stages.

use affine_cat::base::{Absorb, DuplicateTo, Embed, KeepLeft, Link, Piece};
use affine_cat::data::Visit;
use affine_cat::machines::{Driven, DuplicateToTransducer, Machine};
use core::ops::ControlFlow;

// ---------- the domain ----------

#[derive(Clone, Copy)]
struct Entry {
    status: u16,
    bytes: u64,
}

// `DuplicateToTransducer` duplicates the shared input into each machine, so the input must
// be `Unaliased` (independent duplication). `Entry: Clone` already gives
// `Comonoid` via the blanket; we opt into the stronger `Unaliased` marker —
// sound here because `Entry` is `Copy` over plain integers, so the two
// copies share no observable state. (A type with `Rc`/interior mutability
// could NOT make this promise, which is exactly what the bound enforces.)
impl affine_cat::base::Unaliased for Entry {}

// ---------- base: parsing as pure morphisms ----------
//
// Each line -> Entry. We build the parser as a composition of small
// morphisms so the structure is visible; monomorphization fuses it to a
// single function with no closures surviving.

fn parse_line(line: &str) -> Option<Entry> {
    // "STATUS BYTES", whitespace separated (a stand-in for a real format).
    let mut it = line.split_whitespace();
    let status = it.next()?.parse().ok()?;
    let bytes = it.next()?.parse().ok()?;
    Some(Entry { status, bytes })
}

// ---------- machines: running statistics as Moore machines ----------

/// Count entries whose status is >= 400 (client/server errors).
struct ErrorRate {
    errors: u64,
    total: u64,
}
impl Machine for ErrorRate {
    type In = Entry;
    type Out = (u64, u64); // (errors, total)
    fn out(&self) -> (u64, u64) {
        (self.errors, self.total)
    }
    fn update(&mut self, e: Entry) {
        self.total += 1;
        if e.status >= 400 {
            self.errors += 1;
        }
    }
}

/// Total bytes served — a plain running sum.
struct TotalBytes(u64);
impl Machine for TotalBytes {
    type In = Entry;
    type Out = u64;
    fn out(&self) -> u64 {
        self.0
    }
    fn update(&mut self, e: Entry) {
        self.0 += e.bytes;
    }
}

/// Largest single response seen (a running max).
struct MaxBytes(u64);
impl Machine for MaxBytes {
    type In = Entry;
    type Out = u64;
    fn out(&self) -> u64 {
        self.0
    }
    fn update(&mut self, e: Entry) {
        if e.bytes > self.0 {
            self.0 = e.bytes;
        }
    }
}

// ---------- a Visit source over the log lines ----------

/// Visits each successfully-parsed entry, skipping malformed lines. This is
/// the crate's final (push) encoding: the source drives, the sink reacts.
struct ParsedEntries<'a>(&'a str);
impl<'a> Visit<()> for ParsedEntries<'a> {
    type Item = Entry;
    fn visit<R>(
        &mut self,
        _input: (),
        f: &mut impl FnMut(Entry) -> ControlFlow<R>,
    ) -> ControlFlow<R> {
        for line in self.0.lines() {
            if let Some(entry) = parse_line(line) {
                match f(entry) {
                    ControlFlow::Continue(()) => {}
                    br => return br,
                }
            }
        }
        ControlFlow::Continue(())
    }
}

fn main() {
    let log = "\
200 1024
404 256
200 8192
500 512
200 2048
403 128
200 65536";

    // Wire THREE statistics into ONE machine with DuplicateToTransducer: it runs all three
    // over each entry (the entry is Copy — hence Unaliased — so the
    // shared-input fanout is sound and cheap). This is the machine
    // applicative: a machine whose readout is the tuple of all three.
    let stats = DuplicateToTransducer(
        ErrorRate {
            errors: 0,
            total: 0,
        },
        DuplicateToTransducer(TotalBytes(0), MaxBytes(0)),
    );

    // The seam: `Driven` turns that machine into an `Absorb` sink, and the
    // `Visit` source feeds it. ONE pass, no intermediate `Vec<Entry>` — each
    // parsed record flows straight into all three accumulators at once.
    let mut sink = Driven(stats);
    ParsedEntries(log).for_each((), |entry| sink.absorb(entry));

    // Read each accumulator's Moore readout. `DuplicateToTransducer` is the machine
    // applicative (Mealy-shaped: it zips outputs as you step), so we read the
    // final statistics off the inner Moore machines directly — each has a
    // pure `out()`.
    let DuplicateToTransducer(error_rate, DuplicateToTransducer(total_bytes, max_bytes)) = &sink.0;
    let (errs, total) = error_rate.out();
    let sum = total_bytes.out();
    let max = max_bytes.out();
    let pct = if total == 0 {
        0.0
    } else {
        100.0 * errs as f64 / total as f64
    };
    println!("{total} requests | {errs} errors ({pct:.1}%) | {sum} bytes total | {max} max");

    // Demonstrate the pure-pipeline side too: a classifier built by
    // composition, showing base's morphisms fuse to a zero-sized value.
    let classify = Link(
        DuplicateTo(
            Embed(|e: Entry| e.status / 100),   // status class (2,4,5,...)
            Embed(|e: Entry| e.bytes > 10_000), // "large response?"
        ),
        KeepLeft, // keep just the class (projection — discards the bool)
    );
    assert_eq!(core::mem::size_of_val(&classify), 0); // fused to nothing
    let e = Entry {
        status: 404,
        bytes: 256,
    };
    assert_eq!(classify.run(e), 4);

    println!(
        "(classifier pipeline is {} bytes)",
        core::mem::size_of_val(&classify)
    );
}
