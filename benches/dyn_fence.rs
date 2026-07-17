use std::hint::black_box;
use std::time::Instant;

// ===== the two Holes variants, same shapes as the crate =====
trait HolesDyn<T> { fn map_ref<U>(&self, f: &mut dyn FnMut(&T) -> U) -> U; }
trait HolesGen<T> { fn map_ref<U, F: FnMut(&T) -> U>(&self, f: F) -> U; }
impl<T> HolesDyn<T> for Box<T> { fn map_ref<U>(&self, f: &mut dyn FnMut(&T) -> U) -> U { f(self) } }
impl<T> HolesGen<T> for Box<T> { fn map_ref<U, F: FnMut(&T) -> U>(&self, mut f: F) -> U { f(self) } }

enum Tree { Leaf(i64), Node(Box<Tree>, Box<Tree>) }

fn build(depth: u32) -> Tree {
    if depth == 0 { Tree::Leaf(1) } else { Tree::Node(Box::new(build(depth - 1)), Box::new(build(depth - 1))) }
}

// ===== algebras =====
trait Alg { fn leaf(&self, n: i64) -> i64; fn node(&self, a: i64, b: i64) -> i64; }
struct Count;
impl Alg for Count { #[inline] fn leaf(&self, _: i64) -> i64 { 1 } #[inline] fn node(&self, a: i64, b: i64) -> i64 { a + b + 1 } }
struct Mix;
impl Alg for Mix {
    #[inline] fn leaf(&self, n: i64) -> i64 { n.wrapping_mul(0x9E3779B97F4A7C15u64 as i64) ^ 0x5bd1e995 }
    #[inline] fn node(&self, a: i64, b: i64) -> i64 { (a ^ b.rotate_left(13)).wrapping_mul(5).wrapping_add(0xe6546b64) }
}

// ===== drivers, same recursion shape as generated fold =====
fn fold_dyn<A: Alg>(t: &Tree, alg: &A) -> i64 {
    match t {
        Tree::Leaf(n) => alg.leaf(*n),
        Tree::Node(l, r) => {
            let a = HolesDyn::map_ref(l, &mut |c| fold_dyn(c, alg));
            let b = HolesDyn::map_ref(r, &mut |c| fold_dyn(c, alg));
            alg.node(a, b)
        }
    }
}
fn fold_gen<A: Alg>(t: &Tree, alg: &A) -> i64 {
    match t {
        Tree::Leaf(n) => alg.leaf(*n),
        Tree::Node(l, r) => {
            let a = HolesGen::map_ref(l, |c| fold_gen(c, alg));
            let b = HolesGen::map_ref(r, |c| fold_gen(c, alg));
            alg.node(a, b)
        }
    }
}

fn time<F: FnMut() -> i64>(label: &str, nodes: f64, mut f: F) {
    for _ in 0..3 { black_box(f()); } // warmup
    let mut best = f64::MAX;
    for _ in 0..7 {
        let t0 = Instant::now();
        black_box(f());
        let dt = t0.elapsed().as_secs_f64();
        if dt < best { best = dt; }
    }
    println!("{label:22} {:8.2} ns/node   ({:.1} ms total)", best * 1e9 / nodes, best * 1e3);
}

fn main() {
    let depth = 21; // 2^22 - 1 nodes ≈ 4.2M
    let nodes = (2f64.powi(depth as i32 + 1)) - 1.0;
    let t = build(depth);
    let t = black_box(&t);
    time("dyn / Count", nodes, || fold_dyn(t, &Count));
    time("gen / Count", nodes, || fold_gen(t, &Count));
    time("dyn / Mix", nodes, || fold_dyn(t, &Mix));
    time("gen / Mix", nodes, || fold_gen(t, &Mix));
    // erased algebra through generic holes (the compat face, priced)
    let e: &dyn Alg = &Count;
    struct W<'a>(&'a dyn Alg);
    impl Alg for W<'_> { #[inline] fn leaf(&self, n: i64) -> i64 { self.0.leaf(n) } #[inline] fn node(&self, a: i64, b: i64) -> i64 { self.0.node(a, b) } }
    time("gen / dyn-Alg Count", nodes, || fold_gen(t, &W(e)));
    time("fence / Count", nodes, || fold_fence(t, &Count));
    time("fence / Mix", nodes, || fold_fence(t, &Mix));
}

// appended: fence hypothesis — generic holes, but recursion behind a call fence
#[inline(never)]
fn fence_call<A: Alg>(t: &Tree, alg: &A) -> i64 { fold_fence(t, alg) }
fn fold_fence<A: Alg>(t: &Tree, alg: &A) -> i64 {
    match t {
        Tree::Leaf(n) => alg.leaf(*n),
        Tree::Node(l, r) => {
            let a = HolesGen::map_ref(l, |c| fence_call(c, alg));
            let b = HolesGen::map_ref(r, |c| fence_call(c, alg));
            alg.node(a, b)
        }
    }
}
