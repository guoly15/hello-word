Require Import Word.

Open Scope word_scope.

Goal forall w1 w2 w3 w4 : word 32,
  w1 & (w2 | ~w3 & w4) == (w2 | ~w3) & (w4 & w1 | w1 & w2).
Proof.
  weq_bool.
Qed.

Goal forall w : word 32, w | ~wfalse 32 == ~(w & ~w).
Proof.
  weq_bool.
Qed.

Goal forall w1 w2 w3 : word 32, ~ (w2 == w3) ->
  w1 & ~(wof_N 32 1 << w2) & (wof_N 32 1 << w3) == w1 & (wof_N 32 1 << w3).
Proof.
  weq_bool. wand_1_wshl_weqf w2 w3. assumption.
Qed.

Module Word32 : Word with Definition n := 32.
Definition n : nat := 32.
End Word32.

Module RingWord32 := RingWord Word32.
Import RingWord32.

Goal forall w1 w2 w3 w4 : word 32,
  (w1 + w3 - w2 * w4) * w4 + w1 ==
  (w4 + wof_N 32 1) * w1 - w4 * w2 * w4 + w4 * w3.
Proof.
  intros. change 32 with Word32.n; ring.
Qed.
