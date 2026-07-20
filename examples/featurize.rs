//! The cross-spine acceptance example: the whole point of one workspace.
//!
//! `data` produces a token stream (final/visitor encoding); `machines`
//! consumes it as a sink; `base` accumulates. This is creature_feature's
//! `Ftzr` + `Accumulates` — bigram featurization — expressed as instances
//! of the crate's vocabulary, with the `Comonoid` bound landing exactly
//! where the two-output fanout duplicates a token.

use affine_cat::base::{Absorb, Count, Pair};
use affine_cat::data::{accumulate, ArrayWindows};

fn main() {
    let text = b"mississippi";

    // ONE pass over the bigram stream, TWO accumulators (featurize_x2's
    // shape): collect the bigrams AND count them. The token [u8;2] is
    // duplicated into both sinks — the Comonoid bound is why this typechecks.
    let Pair(bigrams, count): Pair<Vec<[u8; 2]>, Count> =
        accumulate(&mut ArrayWindows::<2>, &text[..]);

    println!("bigrams ({}):", count.0);
    for bg in &bigrams {
        println!("  {}{}", bg[0] as char, bg[1] as char);
    }
    assert_eq!(count.0, text.len() - 1); // n-1 bigrams
    assert_eq!(bigrams[0], [b'm', b'i']);

    // The seam from the OTHER direction: a machine driven as a sink.
    // A frequency counter of a specific bigram, as a Moore machine feeding
    // the kernel's Absorb via Driven — data flowing data->machine->kernel.
    use affine_cat::machines::{Driven, Machine};
    struct CountIf([u8; 2], u32);
    impl Machine for CountIf {
        type In = [u8; 2];
        type Out = u32;
        fn out(&self) -> u32 {
            self.1
        }
        fn update(&mut self, bg: [u8; 2]) {
            if bg == self.0 {
                self.1 += 1;
            }
        }
    }
    let mut ssi = Driven(CountIf(*b"ss", 0));
    accumulate_into(&mut ArrayWindows::<2>, &text[..], &mut ssi);
    println!("'ss' occurs {} times", ssi.0.out());
    assert_eq!(ssi.0.out(), 2); // mi-ss-i-ss-ippi

    println!("\ncross-spine seam verified: data -> machines -> base");
}

// A tiny driver that accumulates into an existing sink (accumulate() builds
// a fresh Default one; here we feed a pre-built machine-sink).
fn accumulate_into<I, V, A>(v: &mut V, input: I, sink: &mut A)
where
    V: affine_cat::data::Visit<I>,
    A: Absorb<V::Item>,
{
    v.for_each(input, |t| sink.absorb(t));
}
