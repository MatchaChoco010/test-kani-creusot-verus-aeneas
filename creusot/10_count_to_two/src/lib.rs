use creusot_std::{
    ghost::{
        invariant::{AtomicInvariantSC, Protocol, Tokens, declare_namespace},
        perm::Perm,
        resource::{Authority, Fragment},
    },
    logic::{Id, ra::excl::Excl},
    prelude::*,
    std::{
        sync::{
            atomic_sc::{AtomicU32, ordering::SeqCst},
            committer::Committer,
        },
        thread::{self, JoinHandleExt},
    },
};

declare_namespace! { COUNTER }

struct CounterInv {
    own: Perm<AtomicU32>,
    auth1: Authority<Option<Excl<bool>>>,
    auth2: Authority<Option<Excl<bool>>>,
}

impl Protocol for CounterInv {
    type Public = (AtomicU32, Id, Id);

    #[logic]
    fn public(self) -> Self::Public {
        (*self.own.ward(), self.auth1.id(), self.auth2.id())
    }

    // カウンタの値は「加算済みのスレッド数」と常に一致する
    #[logic(inline)]
    fn protocol(self) -> bool {
        pearlite! {
            self.own.val()@ ==
                if self.auth1@ == Some(Excl(true)) { 1 } else { 0 } +
                if self.auth2@ == Some(Excl(true)) { 1 } else { 0 }
        }
    }
}

#[ensures(result@ == 2)]
pub fn count_to_two() -> u32 {
    let (atomic, own) = AtomicU32::new(0);

    let mut auth1 = Authority::alloc();
    let mut auth2 = Authority::alloc();
    let mut frag1 = ghost!(Fragment::new_unit(auth1.id_ghost()));
    let mut frag2 = ghost!(Fragment::new_unit(auth2.id_ghost()));
    ghost! {
        auth1.update(&mut frag1, snapshot!((Some(Excl(false)), Some(Excl(false)))));
        auth2.update(&mut frag2, snapshot!((Some(Excl(false)), Some(Excl(false)))));
    };

    let inv = AtomicInvariantSC::new(
        ghost!(CounterInv {
            own: own.into_inner(),
            auth1: auth1.into_inner(),
            auth2: auth2.into_inner()
        }),
        snapshot!(COUNTER()),
    );

    thread::scope(|s| {
        let mut frag1: Ghost<&mut _> = frag1.borrow_mut();
        let mut frag2: Ghost<&mut _> = frag2.borrow_mut();
        let inv: Ghost<&_> = inv.borrow();
        let atomic = &atomic;

        let t1 = s.spawn(move |tokens: Ghost<Tokens>| {
            atomic.fetch_add(
                1,
                // fetch_add と同時に不変条件を開き、このスレッドの加算済みフラグを立てる
                ghost! { |c: &mut Committer<_, _, SeqCst, SeqCst>| {
                    inv.open(tokens.into_inner(), |inv: &mut CounterInv| {
                        inv.auth1.update(*frag1, snapshot!((Some(Excl(true)), Some(Excl(true)))));
                        c.shoot_load(&inv.own);
                        c.shoot_store(&mut inv.own);
                    })
                }},
            );
        });

        let t2 = s.spawn(move |tokens: Ghost<Tokens>| {
            atomic.fetch_add(
                1,
                ghost! { |c: &mut Committer<_, _, SeqCst, SeqCst>| {
                    inv.open(tokens.into_inner(), |inv: &mut CounterInv| {
                        inv.auth2.update(*frag2, snapshot!((Some(Excl(true)), Some(Excl(true)))));
                        c.shoot_load(&inv.own);
                        c.shoot_store(&mut inv.own);
                    })
                }},
            );
        });

        t1.join_unwrap();
        t2.join_unwrap();
    });

    // 手元の Fragment から両スレッドが加算済みであることを導き、atomic の所有権を取り戻す
    let own = ghost! {
        let inv = inv.into_inner().into_inner();
        inv.auth1.frag_lemma(&frag1);
        inv.auth2.frag_lemma(&frag2);
        inv.own
    };
    atomic.into_inner(own)
}
