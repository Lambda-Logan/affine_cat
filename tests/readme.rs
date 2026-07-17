// Every code block destined for README.md, compiled and run verbatim.

#[test]
fn snippet_quickstart_machines() {
    use affine_cat::machines::{DuplicateToMachine, Machine};

    struct Total(u64);
    impl Machine for Total {
        type In = u64;
        type Out = u64;
        fn out(&self) -> u64 {
            self.0
        }
        fn update(&mut self, x: u64) {
            self.0 += x;
        }
    }

    struct Max(u64);
    impl Machine for Max {
        type In = u64;
        type Out = u64;
        fn out(&self) -> u64 {
            self.0
        }
        fn update(&mut self, x: u64) {
            self.0 = self.0.max(x);
        }
    }

    let mut stats = DuplicateToMachine(Total(0), Max(0));
    for x in [3, 9, 4] {
        stats.update(x);
    }
    assert_eq!(stats.out(), (16, 9));
}

#[test]
fn snippet_pieces() {
    use affine_cat::base::{Embed, Piece, PieceExt};

    let status_class = Embed(|status: u16| status / 100);
    let is_server_error = Embed(|class: u16| class == 5);
    let classify = status_class.link(is_server_error);

    assert!(classify.run(503));
    assert!(!classify.run(404));
    assert_eq!(core::mem::size_of_val(&classify), 0);
}

#[test]
fn snippet_duplicate_to() {
    use affine_cat::base::{Embed, Piece, PieceExt};

    let p = Embed(|s: String| s.len()).duplicate_to(Embed(|s: String| s.to_uppercase()));
    assert_eq!(p.run("dia".into()), (3, "DIA".into()));
}

#[test]
fn snippet_result_pipelines() {
    use affine_cat::base::{consume_result, Embed, Piece, PieceExt};

    let parse = Embed(|s: &str| s.parse::<i64>().map_err(|_| "not a number"));
    let positive = Embed(|n: i64| if n > 0 { Ok(n) } else { Err("not positive") });

    let p = parse.link_ok(positive);
    assert_eq!(p.run("42"), Ok(42));
    assert_eq!(p.run("-7"), Err("not positive"));
    assert_eq!(p.run("x"), Err("not a number"));

    let settle = consume_result(Embed(|n: i64| n), Embed(|_e: &str| -1));
    assert_eq!(settle.run(p.run("42")), 42);
    assert_eq!(settle.run(p.run("x")), -1);
}

#[test]
fn snippet_one_pass_two_answers() {
    use affine_cat::base::{Count, Pair};
    use affine_cat::data::{accumulate, ArrayWindows};

    let text = b"banana";
    let Pair(bigrams, n): Pair<Vec<[u8; 2]>, Count> = accumulate(&mut ArrayWindows::<2>, &text[..]);
    assert_eq!(n.0, 5);
    assert_eq!(bigrams[0], [b'b', b'a']);
}

#[test]
fn snippet_machine_as_sink() {
    use affine_cat::base::Absorb;
    use affine_cat::data::{ArrayWindows, Visit};
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

    let mut ss = Driven(CountIf([b's', b's'], 0));
    ArrayWindows::<2>.for_each(&b"mississippi"[..], |bg| ss.absorb(bg));
    assert_eq!(ss.0.out(), 2);
}

#[test]
fn snippet_cps() {
    use affine_cat::cps::{Embed, Piece, PieceExt};
    use core::ops::ControlFlow;

    struct Each;
    impl Piece<[u32]> for Each {
        type Out = u32;
        fn run<R>(
            &self,
            env: &mut (),
            a: &[u32],
            k: &mut dyn FnMut(&mut (), &u32) -> ControlFlow<R>,
        ) -> ControlFlow<R> {
            for x in a {
                k(env, x)?;
            }
            ControlFlow::Continue(())
        }
    }

    let pipe = Each.link(Embed(|x: &u32| x * 2));
    let mut out = Vec::new();
    let _: ControlFlow<()> = pipe.run(&mut (), &[1, 2, 3][..], &mut |_, y| {
        out.push(*y);
        ControlFlow::Continue(())
    });
    assert_eq!(out, [2, 4, 6]);
}

#[test]
fn snippet_weighted() {
    use affine_cat::machines::{run_history, Machine};
    use affine_cat::weighted::{Prod, Sum};

    #[derive(Clone, Copy)]
    struct Has(char, bool);
    impl Machine for Has {
        type In = char;
        type Out = bool;
        fn out(&self) -> bool {
            self.1
        }
        fn update(&mut self, c: char) {
            if c == self.0 {
                self.1 = true;
            }
        }
    }

    let mut union = Sum::new(Has('a', false), Has('b', false));
    assert!(run_history(&mut union, "xa".chars()));
    let mut both = Prod::new(Has('a', false), Has('b', false));
    assert!(!run_history(&mut both, "xa".chars()));
}

#[test]
fn snippet_functors() {
    use affine_cat::data::{MapMut, MapOnce, Zip};

    fn double_all<T: MapMut<i32>>(t: T) -> T::Output<i32> {
        t.fmap(|x| x * 2)
    }
    assert_eq!(double_all(vec![1, 2]), vec![2, 4]);
    assert_eq!(double_all(Some(3)), Some(6));

    let owned = String::from("tag");
    assert_eq!(
        Some(1).fmap_once(move |n| format!("{owned}:{n}")),
        Some("tag:1".to_string())
    );

    let a: Result<i32, &str> = Ok(1);
    let b: Result<&str, &str> = Err("boom");
    assert_eq!(a.zip(b), Err("boom"));
}

#[test]
fn snippet_lens() {
    use affine_cat::base::lens;

    struct Engine {
        rpm: u32,
    }
    struct Car {
        engine: Engine,
    }

    let rpm = lens(|c: &mut Car| &mut c.engine, |e: &mut Engine| &mut e.rpm);
    let mut car = Car {
        engine: Engine { rpm: 800 },
    };
    *rpm(&mut car) = 6000;
    assert_eq!(*rpm(&mut car), 6000);
}

#[test]
fn snippet_run_history_property() {
    use affine_cat::machines::{run_history, Machine};

    struct Sum(u64);
    impl Machine for Sum {
        type In = u64;
        type Out = u64;
        fn out(&self) -> u64 {
            self.0
        }
        fn update(&mut self, x: u64) {
            self.0 += x;
        }
    }

    let history = [1u64, 2, 3, 4];
    assert_eq!(
        run_history(&mut Sum(0), history),
        history.iter().sum::<u64>()
    );
}

// The two verbatim fenced ```rust blocks from README.md, run exactly as printed.

#[test]
fn readme_block_quickstart() {
    use affine_cat::base::{Count, Pair};
    use affine_cat::data::{accumulate, ArrayWindows};

    let text = b"mississippi";
    let Pair(bigrams, count): Pair<Vec<[u8; 2]>, Count> =
        accumulate(&mut ArrayWindows::<2>, &text[..]);
    assert_eq!(count.0, 10);
    assert_eq!(bigrams[0], [b'm', b'i']);
}

#[test]
fn readme_block_classify() {
    use affine_cat::base::{Embed, Piece, PieceExt};

    let classify =
        Embed(|status: u16| status / 100).link(Embed(|class: u16| matches!(class, 4 | 5)));
    assert!(classify.run(404));
    assert_eq!(core::mem::size_of_val(&classify), 0); // fused away
}

#[test]
fn readme_block_machine() {
    use affine_cat::machines::{run_history, Machine};

    struct MaxSeen(u64);
    impl Machine for MaxSeen {
        type In = u64;
        type Out = u64;
        fn out(&self) -> u64 {
            self.0
        }
        fn update(&mut self, x: u64) {
            self.0 = self.0.max(x)
        }
    }
    assert_eq!(run_history(&mut MaxSeen(0), [3, 9, 4]), 9);
}

#[test]
fn readme_block_cata() {
    use affine_cat::cata::{FoldAlg, Pair};
    use affine_cat_derive::Recursive;

    #[derive(Recursive)]
    enum Expr {
        Lit(i64),
        Add(Box<Expr>, Box<Expr>),
    }

    struct Eval;
    impl FoldAlg<Expr, ()> for Eval {
        type Out = i64;
        fn reduce<'a>(&self, _: &(), l: ExprLayer<'a, i64>) -> i64
        where
            Expr: 'a,
        {
            match l {
                ExprLayer::Lit(n) => *n,
                ExprLayer::Add(a, b) => a + b,
            }
        }
    }

    struct Depth;
    impl FoldAlg<Expr, ()> for Depth {
        type Out = usize;
        fn reduce<'a>(&self, _: &(), l: ExprLayer<'a, usize>) -> usize
        where
            Expr: 'a,
        {
            match l {
                ExprLayer::Lit(_) => 0,
                ExprLayer::Add(a, b) => a.max(b) + 1,
            }
        }
    }

    let e = Expr::Add(
        Box::new(Expr::Lit(2)),
        Box::new(Expr::Add(Box::new(Expr::Lit(3)), Box::new(Expr::Lit(4)))),
    );
    // one traversal, two algebras — no Clone bound anywhere
    let (val, depth) = e.fold(&(), &Pair(&Eval, &Depth));
    assert_eq!((val, depth), (9, 2));
}
