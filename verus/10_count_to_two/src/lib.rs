use std::sync::Arc;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::atomic_ghost::*;
use vstd::prelude::*;
use vstd::thread::spawn;

verus! {

tokenized_state_machine!(
    counting {
        fields {
            #[sharding(variable)]
            pub counter: int,

            #[sharding(variable)]
            pub inc_a: bool,

            #[sharding(variable)]
            pub inc_b: bool,
        }

        // counter は「加算済みのスレッド数」と常に一致する
        #[invariant]
        pub fn main_inv(&self) -> bool {
            self.counter == (if self.inc_a { 1 as int } else { 0 }) + (if self.inc_b { 1 as int } else { 0 })
        }

        init!{
            initialize() {
                init counter = 0;
                init inc_a = false;
                init inc_b = false;
            }
        }

        transition!{
            tr_inc_a() {
                require(!pre.inc_a);
                update counter = pre.counter + 1;
                update inc_a = true;
            }
        }

        transition!{
            tr_inc_b() {
                require(!pre.inc_b);
                update counter = pre.counter + 1;
                update inc_b = true;
            }
        }

        property!{
            increment_will_not_overflow_u32() {
                assert 0 <= pre.counter < 0xffff_ffff;
            }
        }

        property!{
            finalize() {
                require(pre.inc_a);
                require(pre.inc_b);
                assert pre.counter == 2;
            }
        }

        #[inductive(tr_inc_a)]
        fn tr_inc_a_preserves(pre: Self, post: Self) {
        }

        #[inductive(tr_inc_b)]
        fn tr_inc_b_preserves(pre: Self, post: Self) {
        }

        #[inductive(initialize)]
        fn initialize_inv(post: Self) {
        }
    }
);

struct_with_invariants!{
    pub struct Global {
        pub atomic: AtomicU32<_, counting::counter, _>,
        pub instance: Tracked<counting::Instance>,
    }

    spec fn wf(&self) -> bool {
        // 実際の atomic の値とゴーストの counter トークンの値を結び付ける
        invariant on atomic with (instance) is (v: u32, g: counting::counter) {
            g.instance_id() == instance@.id()
            && g.value() == v as int
        }
    }
}

pub fn count_to_two() -> (r: Result<u32, ()>)
    ensures
        r matches Ok(n) ==> n == 2,
{
    let tracked (
        Tracked(instance),
        Tracked(counter_token),
        Tracked(inc_a_token),
        Tracked(inc_b_token),
    ) = counting::Instance::initialize();
    let tr_instance: Tracked<counting::Instance> = Tracked(instance.clone());
    let atomic = AtomicU32::new(Ghost(tr_instance), 0, Tracked(counter_token));
    let global = Global { atomic, instance: Tracked(instance.clone()) };
    let global_arc = Arc::new(global);

    let global_arc1 = global_arc.clone();
    let join_handle1 = spawn(
        (move || -> (new_token: Tracked<counting::inc_a>)
            ensures
                new_token@.instance_id() == instance.id() && new_token@.value() == true,
            {
                let tracked mut token = inc_a_token;
                let globals = &*global_arc1;
                let _ =
                    // fetch_add と同時に状態機械の遷移 tr_inc_a を実行する
                    atomic_with_ghost!(&globals.atomic => fetch_add(1);
                        ghost c => {
                            globals.instance.borrow().increment_will_not_overflow_u32(&c);
                            globals.instance.borrow().tr_inc_a(&mut c, &mut token);
                        }
                    );
                Tracked(token)
            }),
    );

    let global_arc2 = global_arc.clone();
    let join_handle2 = spawn(
        (move || -> (new_token: Tracked<counting::inc_b>)
            ensures
                new_token@.instance_id() == instance.id() && new_token@.value() == true,
            {
                let tracked mut token = inc_b_token;
                let globals = &*global_arc2;
                let _ =
                    atomic_with_ghost!(&globals.atomic => fetch_add(1);
                        ghost c => {
                            globals.instance.borrow().increment_will_not_overflow_u32(&c);
                            globals.instance.borrow().tr_inc_b(&mut c, &mut token);
                        }
                    );
                Tracked(token)
            }),
    );

    let tracked inc_a_token;
    match join_handle1.join() {
        Result::Ok(token) => {
            proof {
                inc_a_token = token.get();
            }
        },
        _ => {
            return Err(());
        },
    };
    let tracked inc_b_token;
    match join_handle2.join() {
        Result::Ok(token) => {
            proof {
                inc_b_token = token.get();
            }
        },
        _ => {
            return Err(());
        },
    };

    let global = &*global_arc;
    let x =
        atomic_with_ghost!(&global.atomic => load();
        ghost c => {
            // inc_a と inc_b の両トークンが true であることから counter == 2 を導く
            instance.finalize(&c, &inc_a_token, &inc_b_token);
        }
    );
    Ok(x)
}

} // verus!
