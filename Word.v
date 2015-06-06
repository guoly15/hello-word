Require Import Bool Setoid ZArith.
Require Export List.
Require Omega.

(*********************************firstn/skipn*********************************)

Lemma firstn_nil : forall {A : Type} (n : nat), firstn n (@nil A) = @nil A.
Proof.
  intros ? []; reflexivity.
Qed.

Lemma skipn_nil : forall {A : Type} (n : nat), skipn n (@nil A) = @nil A.
Proof.
  intros ? []; reflexivity.
Qed.

Notation length_firstn := firstn_length.

Lemma length_skipn : forall {A : Type} (n : nat) (l : list A),
  length (skipn n l) = length l - n.
Proof.
  intros ? n; induction n as [| n' IHn']; intro l.
  - apply minus_n_O.
  - destruct l.
    + reflexivity.
    + apply IHn'.
Qed.

Lemma skipn_whole : forall {A : Type} (n : nat) (l : list A),
  n >= length l -> skipn n l = nil.
Proof.
  intros ? n l ?.
  assert (length (skipn n l) = 0). {
    rewrite length_skipn.
    omega.
  }
  destruct (skipn n l).
  - reflexivity.
  - discriminate.
Qed.

Lemma firstn_whole : forall {A : Type} (n : nat) (l : list A),
  n >= length l -> firstn n l = l.
Proof.
  intros ? n l ?.
  rewrite <- (firstn_skipn n l) at 2.
  rewrite skipn_whole; try assumption.
  apply app_nil_end.
Qed.

Lemma firstn_firstn : forall {A : Type} (n m : nat) (l : list A),
  firstn n (firstn m l) = firstn (min n m) l.
Proof.
  intros ? n m l; destruct (le_ge_dec n m).
  - rewrite min_l; try assumption.
    generalize dependent m; generalize dependent n;
    induction l as [| h t IHt]; intros n m ?.
    + rewrite (firstn_nil m). reflexivity.
    + destruct n.
      * reflexivity.
      *{destruct m.
        - omega.
        - simpl. f_equal.
          apply IHt. omega.
      }
  - rewrite min_r; try assumption.
    apply firstn_whole.
    rewrite length_firstn.
    apply (le_trans _ m).
    + apply NPeano.Nat.le_min_l.
    + assumption.
Qed.

(******************************************************************************)

(**********************************list bool***********************************)

Delimit Scope word_scope with word.

Local Open Scope word_scope.

Notation "l ~ b" := (b :: l)
 (at level 7, left associativity, format "l '~' b") : word_scope.
Notation "l ~ 0" := (false :: l)
 (at level 7, left associativity, format "l '~' '0'") : word_scope.
Notation "l ~ 1" := (true :: l)
 (at level 7, left associativity, format "l '~' '1'") : word_scope.

Notation "w1 # w2" := (w2 ++ w1)
 (at level 60, right associativity) : word_scope.

Fixpoint list_bool_to_N (l : list bool) : N :=
  match l with
  | nil => N0
  | t~0 => N.double (list_bool_to_N t)
  | t~1 => N.succ_double (list_bool_to_N t)
  end.

Fixpoint list_bool_of_N (len : nat) (n : N) : list bool :=
  match len with
  | 0 => nil
  | S len' => match n with
              | N0 => (list_bool_of_N len' N0)~0
              | Npos xH => (list_bool_of_N len' N0)~1
              | Npos (xO p) => (list_bool_of_N len' (Npos p))~0
              | Npos (xI p) => (list_bool_of_N len' (Npos p))~1
              end
  end.

Notation falsen := (fun n : nat => nat_iter n (cons false) nil).
Notation truen := (fun n : nat => nat_iter n (cons true) nil).

Fixpoint blist {A B C : Type} (f : A -> B -> C) (l1 : list A) (l2 : list B) :=
  match l1, l2 with
  | nil, _ => nil
  | _, nil => nil
  | h1 :: t1, h2 :: t2 => f h1 h2 :: blist f t1 t2
  end.

Lemma length_of_N : forall (len : nat) (n : N),
  length (list_bool_of_N len n) = len.
Proof.
  intro len; induction len; intro n.
  - reflexivity.
  - destruct n as [| []]; simpl; f_equal; trivial.
Qed.

Lemma length_iter_cons : forall {A : Type} (n : nat) (h : A) (t : list A),
  length (nat_iter n (cons h) t) = n + length t.
Proof.
  intros ? n ? ?; induction n.
  - reflexivity.
  - simpl. f_equal. assumption.
Qed.

Lemma iter_cons_split : forall {A : Type} (n m : nat) (h : A),
  nat_iter (n + m) (cons h) nil = nat_iter n (cons h) nil ++
                                  nat_iter m (cons h) nil.
Proof.
  intros ? n ? ?; induction n.
  - reflexivity.
  - simpl. f_equal. assumption.
Qed.

Lemma firstn_iter_cons : forall {A : Type} (n m : nat) (h : A),
  firstn n (nat_iter m (cons h) nil) = nat_iter (min n m) (cons h) nil.
Proof.
  intros ? n m ?.
  generalize dependent m;
  induction n; intro m.
  - reflexivity.
  - destruct m.
    + reflexivity.
    + simpl. f_equal. trivial.
Qed.

Lemma length_blist :
  forall {A B C : Type} (f : A -> B -> C) (l1 : list A) (l2 : list B),
  length (blist f l1 l2) = min (length l1) (length l2).
Proof.
  intros ? ? ? ? l1; induction l1; intro l2.
  - reflexivity.
  - destruct l2.
    + reflexivity.
    + simpl. f_equal. trivial.
Qed.

Lemma blist_firstn :
  forall {A B C : Type} (f : A -> B -> C) (l1 : list A) (l2 : list B) n m,
  blist f (firstn n l1) (firstn m l2) = firstn (min n m) (blist f l1 l2).
Proof.
  intros ? ? ? ? l1 l2 n.
  generalize dependent l2; generalize dependent l1;
  induction n; intros l1 l2 m.
  - reflexivity.
  - destruct l1, l2, m; try reflexivity.
    simpl. f_equal. trivial.
Qed.

Lemma blist_app :
  forall {A B C : Type} (f : A -> B -> C) (l1 l1' : list A) (l2 l2' : list B),
  length l1 = length l2 ->
  blist f (l1 ++ l1') (l2 ++ l2') = (blist f l1 l2) ++ (blist f l1' l2').
Proof.
  intros ? ? ? ? l1 ? l2 ?.
  generalize dependent l2;
  induction l1; intros l2 ?.
  - destruct l2; reflexivity || discriminate.
  - destruct l2.
    + discriminate.
    + simpl. f_equal. auto.
Qed.

Lemma blist_andb_falsen_l : forall (n : nat) (l : list bool),
  blist andb (falsen n) l = falsen (min n (length l)).
Proof.
  intro n; induction n; intro l.
  - reflexivity.
  - destruct l.
    + reflexivity.
    + simpl. f_equal. trivial.
Qed.

Lemma blist_andb_falsen_r : forall (l : list bool) (n : nat),
  blist andb l (falsen n) = falsen (min (length l) n).
Proof.
  intro l; induction l; intro n.
  - reflexivity.
  - destruct n.
    + reflexivity.
    + simpl. f_equal.
      * apply andb_false_r.
      * trivial.
Qed.

(******************************************************************************)

(*************************************word*************************************)

Definition word (n : nat) : Set := {l : list bool | length l = n}.

Definition weq {n m : nat} (w1 : word n) (w2 : word m) : Prop :=
  match w1, w2 with exist l1 _, exist l2 _ => l1 = l2 end.
Infix "==" := weq (at level 80, no associativity) : word_scope.

Lemma weq_refl : forall {n : nat} (w : word n), w == w.
Proof.
  intros ? w; destruct w.
  reflexivity.
Qed.

Lemma weq_sym : forall {n m : nat} (w1 : word n) (w2 : word m),
  w1 == w2 -> w2 == w1.
Proof.
  intros ? ? w1 w2; destruct w1, w2.
  apply eq_sym.
Qed.

Lemma weq_trans :
  forall {n m l : nat} (w1 : word n) (w2 : word m) (w3 : word l),
  w1 == w2 -> w2 == w3 -> w1 == w3.
Proof.
  intros ? ? ? w1 w2 w3; destruct w1, w2, w3.
  apply eq_trans.
Qed.

Add Parametric Relation (n : nat) : (word n) weq
  reflexivity proved by weq_refl
  symmetry proved by weq_sym
  transitivity proved by weq_trans as weq_rel.

Definition wto_N {n : nat} (w : word n) : N :=
  let (l, _) := w in list_bool_to_N l.

Definition wof_N (len : nat) (n : N) : word len.
  refine (exist _ (list_bool_of_N len n) _).
  apply length_of_N.
Defined.

Lemma wto_N_id : forall {n : nat} (w : word n), wof_N n (wto_N w) == w.
Proof.
  intros ? w; destruct w as [l Hl]; subst; simpl; induction l as [| h t IHt].
  - reflexivity.
  - destruct h; simpl; destruct (list_bool_to_N t); simpl; congruence.
Qed.

Lemma wof_N_mod : forall (len : nat) (n : N),
  wto_N (wof_N len n) = (n mod (Npos (shift_nat len xH)))%N.
Proof.
  intro len; simpl; induction len as [| len' IHlen']; intro n.
  - symmetry; apply N.mod_1_r.
  - destruct n as [| []]; simpl; rewrite IHlen'; simpl.
    + symmetry; apply N.mod_0_l. discriminate.
    + rewrite <- (N.mod_small (N.succ_double _) (Npos (shift_nat (S len') 1))).
      Focus 2.
        change (Npos (shift_nat (S len') 1))
        with (N.double (Npos (shift_nat len' 1))).
        apply N.succ_double_lt. apply N.mod_lt. discriminate.
      rewrite N.succ_double_spec.
      rewrite <- N.mul_mod_distr_l; try discriminate.
      rewrite N.add_mod_idemp_l; try discriminate.
      reflexivity.
    + rewrite N.double_spec.
      rewrite <- N.mul_mod_distr_l; try discriminate.
      reflexivity.
    + symmetry; apply N.mod_1_l. reflexivity.
Qed.

Lemma wof_N_weq : forall {len : nat} (n : N) (w : word len),
  (n mod (Npos (shift_nat len xH)))%N = wto_N w -> wof_N len n == w.
Proof.
  assert (H0 : forall n1 n2 : N, N.succ_double n1 <> N.double n2)
  by (intros [] []; discriminate).
  intros ? n w; destruct w as [l Hl]; subst; simpl.
  generalize dependent n;
  induction l as [| h t IHt]; intros n H.
  - reflexivity.
  - destruct n as [| [p | p |]].
    + rewrite N.mod_0_l in H; try discriminate.
      destruct h; simpl in *.
      * destruct (list_bool_to_N t); discriminate.
      * f_equal. apply IHt. rewrite N.mod_0_l; try discriminate.
        destruct (list_bool_to_N t); reflexivity || discriminate.
    + replace (_ mod _)%N
      with (N.succ_double (Npos p mod Npos (shift_nat (length t) 1))) in H.
      Focus 2.
        rewrite <- (N.mod_small (N.succ_double _)
                                (N.pos (shift_nat (S (length t)) 1))). Focus 2.
          change (N.pos (shift_nat (S (length t)) 1))
          with (N.double (N.pos (shift_nat (length t) 1))).
          apply N.succ_double_lt. apply N.mod_lt. discriminate.
        rewrite N.succ_double_spec.
        rewrite <- N.mul_mod_distr_l; try discriminate.
        apply N.add_mod_idemp_l. discriminate.
      destruct h; simpl in *.
      * f_equal. apply IHt. apply N.succ_double_inj. assumption.
      * elim (H0 _ _ H).
    + replace (_ mod _)%N
      with (N.double (Npos p mod Npos (shift_nat (length t) 1))) in H.
      Focus 2.
        rewrite N.double_spec. rewrite <- N.mul_mod_distr_l; try discriminate.
        reflexivity.
      destruct h; simpl in *.
      * elim (H0 _ _ (eq_sym H)).
      * f_equal. apply IHt. apply N.double_inj. assumption.
    + rewrite N.mod_1_l in H; try reflexivity.
      destruct h; simpl in *.
      * f_equal. apply IHt. rewrite N.mod_0_l; try discriminate.
        destruct (list_bool_to_N t); reflexivity || discriminate.
      * destruct (list_bool_to_N t); discriminate.
Qed.

Lemma weq_iff_Neq : forall {n : nat} (w1 w2 : word n),
  w1 == w2 <-> wto_N w1 = wto_N w2.
Proof.
  intros ? w1 w2; split; intro H.
  - destruct w1, w2; simpl in *; subst. reflexivity.
  - rewrite <- (wto_N_id w1). rewrite H. apply wto_N_id.
Qed.

Definition wfalse (n : nat) : word n.
  refine (exist _ (falsen n) _).
  rewrite length_iter_cons.
  apply plus_0_r.
Defined.

Lemma wto_N_wfalse : forall n : nat, wto_N (wfalse n) = N0.
Proof.
  intro n; simpl; induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Lemma wof_N_0 : forall n : nat, wof_N n 0 == wfalse n.
Proof.
  intro n; induction n.
  - reflexivity.
  - simpl. f_equal. assumption.
Qed.

Definition wtrue (n : nat) : word n.
  refine (exist _ (truen n) _).
  rewrite length_iter_cons.
  apply plus_0_r.
Defined.

Definition wnot {n : nat} (w : word n) : word n.
  refine (let (l, _) := w in exist _ (map negb l) _).
  rewrite map_length.
  assumption.
Defined.
Notation "~ w" := (wnot w) (at level 75, right associativity) : word_scope.

Add Parametric Morphism (n : nat) : (@wnot n) with
  signature weq ==> weq as wnot_mor.
Proof.
  intros w w'; destruct w, w'; simpl; intro.
  subst. reflexivity.
Qed.

Definition wor {n : nat} (w1 w2 : word n) : word n.
  refine (match w1, w2 with
            exist l1 H1, exist l2 H2 => exist _ (blist orb l1 l2) _
          end).
  rewrite length_blist.
  rewrite H1. rewrite H2.
  apply NPeano.Nat.min_id.
Defined.
Infix "|" := wor (at level 77, left associativity) : word_scope.

Add Parametric Morphism (n : nat) : (@wor n) with
  signature weq ==> weq ==> weq as wor_mor.
Proof.
  intros w1 w1' ? w2 w2' ?; destruct w1, w1', w2, w2'; simpl in *.
  subst. reflexivity.
Qed.

Definition wand {n : nat} (w1 w2 : word n) : word n.
  refine (match w1, w2 with
            exist l1 H1, exist l2 H2 => exist _ (blist andb l1 l2) _
          end).
  rewrite length_blist.
  rewrite H1. rewrite H2.
  apply NPeano.Nat.min_id.
Defined.
Infix "&" := wand (at level 76, left associativity) : word_scope.

Add Parametric Morphism (n : nat) : (@wand n) with
  signature weq ==> weq ==> weq as wand_mor.
Proof.
  intros w1 w1' ? w2 w2' ?; destruct w1, w1', w2, w2'; simpl in *.
  subst. reflexivity.
Qed.

Definition wshl {n : nat} (w1 w2 : word n) : word n.
  refine (let (l1, _) := w1 in
            exist _ (firstn n (l1 # falsen (N.to_nat (wto_N w2)))) _).
  rewrite length_firstn. rewrite app_length. rewrite length_iter_cons.
  apply min_l. omega.
Defined.
Infix "<<" := wshl (at level 65, left associativity) : word_scope.

Add Parametric Morphism (n : nat) : (@wshl n) with
  signature weq ==> weq ==> weq as wshl_mor.
Proof.
  intros w1 w1' ? w2 w2' ?; destruct w1, w1', w2, w2'; simpl in *.
  subst. reflexivity.
Qed.

Definition wshr {n : nat} (w1 w2 : word n) : word n.
  refine (let (l1, _) := w1 in
            exist _ (skipn (N.to_nat (wto_N w2))
                           (falsen (N.to_nat (wto_N w2)) # l1)) _).
  rewrite length_skipn. rewrite app_length. rewrite length_iter_cons.
  simpl; omega.
Defined.
Infix ">>" := wshr (at level 65, left associativity) : word_scope.

Add Parametric Morphism (n : nat) : (@wshr n) with
  signature weq ==> weq ==> weq as wshr_mor.
Proof.
  intros w1 w1' ? w2 w2' ?; destruct w1, w1', w2, w2'; simpl in *.
  subst. reflexivity.
Qed.

Definition wsar {n : nat} (w1 w2 : word n) : word n.
  refine (let (l1, _) := w1 in
            exist _ (skipn (N.to_nat (wto_N w2))
                           ((nat_iter (N.to_nat (wto_N w2))
                                      (cons (last l1 false)) nil)
                           # l1)) _).
  rewrite length_skipn. rewrite app_length. rewrite length_iter_cons.
  simpl; omega.
Defined.
Infix ">->" := wsar (at level 65, left associativity) : word_scope.

Add Parametric Morphism (n : nat) : (@wsar n) with
  signature weq ==> weq ==> weq as wsar_mor.
Proof.
  intros w1 w1' ? w2 w2' ?; destruct w1, w1', w2, w2'; simpl in *.
  subst. reflexivity.
Qed.

Definition wopp {n : nat} (w : word n) : word n :=
  wof_N n (N.succ (wto_N (~w))).
Notation "- w" := (wopp w) (at level 35, right associativity) : word_scope.

Add Parametric Morphism (n : nat) : (@wopp n) with
  signature weq ==> weq as wopp_mor.
Proof.
  intros w w'; destruct w, w'; simpl; intro.
  subst. reflexivity.
Qed.

Definition wadd {n : nat} (w1 w2 : word n) : word n :=
  wof_N n (wto_N w1 + wto_N w2).
Infix "+" := wadd (at level 50, left associativity) : word_scope.

Add Parametric Morphism (n : nat) : (@wadd n) with
  signature weq ==> weq ==> weq as wadd_mor.
Proof.
  intros w1 w1' ? w2 w2' ?; destruct w1, w1', w2, w2'; simpl in *.
  subst. reflexivity.
Qed.

Definition wsub {n : nat} (w1 w2 : word n) : word n := w1 + (- w2).
Infix "-" := wsub (at level 50, left associativity) : word_scope.

Add Parametric Morphism (n : nat) : (@wsub n) with
  signature weq ==> weq ==> weq as wsub_mor.
Proof.
  unfold wsub. intros w1 w1' H1 w2 w2' H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Definition wmul {n : nat} (w1 w2 : word n) : word n :=
  wof_N n (wto_N w1 * wto_N w2).
Infix "*" := wmul (at level 40, left associativity) : word_scope.

Add Parametric Morphism (n : nat) : (@wmul n) with
  signature weq ==> weq ==> weq as wmul_mor.
Proof.
  intros w1 w1' ? w2 w2' ?; destruct w1, w1', w2, w2'; simpl in *.
  subst. reflexivity.
Qed.

(******************************************************************************)

(***********************************boolean************************************)

Lemma wand_assoc : forall {n : nat} (w1 w2 w3 : word n),
  w1 & (w2 & w3) == w1 & w2 & w3.
Proof.
  intros ? w1 w2 w3;
  destruct w1 as [l1 Hl1], w2 as [l2 Hl2], w3 as [l3 Hl3]; simpl.
  clear; generalize dependent l3; generalize dependent l2;
  induction l1; intros l2 l3.
  - reflexivity.
  - destruct l2, l3; try reflexivity; simpl. f_equal.
    + apply andb_assoc.
    + trivial.
Qed.

Lemma wand_comm : forall {n : nat} (w1 w2 : word n),
  w1 & w2 == w2 & w1.
Proof.
  intros ? w1 w2; destruct w1 as [l1 Hl1], w2 as [l2 Hl2]; simpl.
  clear; generalize dependent l2;
  induction l1; intro l2; destruct l2; try reflexivity.
  simpl. f_equal.
  - apply andb_comm.
  - trivial.
Qed.

Lemma wand_wnot_r : forall {n : nat} (w : word n), w & ~w == wfalse n.
Proof.
  intros ? w; destruct w as [l Hl]; subst; simpl; induction l.
  - reflexivity.
  - simpl. f_equal.
    + apply andb_negb_r.
    + assumption.
Qed.

Lemma weq_iff : forall {n : nat} (w1 w2 : word n),
  w1 == w2 <-> w1 & ~w2 == wfalse n /\ w2 & ~w1 == wfalse n.
Proof.
  intros ? w1 w2; split.
  - intro H. rewrite <- H.
    refine ((fun p => conj p p) _).
    clear; destruct w1 as [l1 Hl1]; subst; simpl; induction l1.
    + reflexivity.
    + simpl. f_equal.
      * apply andb_negb_r.
      * assumption.
  - destruct w1 as [l1 Hl1], w2 as [l2 Hl2]; subst; simpl.
    generalize dependent l2;
    induction l1 as [| h1 t1 IHt1]; intros l2 H [H1 H2].
    + destruct l2.
      * reflexivity.
      * discriminate.
    + destruct l2 as [| h2 t2].
      * discriminate.
      * destruct h1, h2; try discriminate; f_equal;
        inversion H; inversion H1; inversion H2; auto.
Qed.

Lemma wnot_involutive : forall {n : nat} (w : word n), ~~w == w.
Proof.
  intros ? w; destruct w as [l Hl]; simpl; clear; induction l.
  - reflexivity.
  - simpl. f_equal.
    + apply negb_involutive.
    + assumption.
Qed.

Lemma wnot_wor : forall {n : nat} (w1 w2 : word n), ~(w1 | w2) == ~w1 & ~w2.
Proof.
  intros ? w1 w2; destruct w1 as [l1 Hl1], w2 as [l2 Hl2]; simpl.
  clear; generalize dependent l2;
  induction l1; intro l2.
  - reflexivity.
  - destruct l2.
    + reflexivity.
    + simpl. f_equal.
      * apply negb_orb.
      * trivial.
Qed.

Lemma wnot_wand : forall {n : nat} (w1 w2 : word n), ~(w1 & w2) == ~w1 | ~w2.
Proof.
  intros ? w1 w2; destruct w1 as [l1 Hl1], w2 as [l2 Hl2]; simpl.
  clear; generalize dependent l2;
  induction l1; intro l2.
  - reflexivity.
  - destruct l2.
    + reflexivity.
    + simpl. f_equal.
      * apply negb_andb.
      * trivial.
Qed.

Lemma wand_wor_distrib_l : forall {n : nat} (w1 w2 w3 : word n),
  (w1 | w2) & w3 == w1 & w3 | w2 & w3.
Proof.
  intros ? w1 w2 w3;
  destruct w1 as [l1 Hl1], w2 as [l2 Hl2], w3 as [l3 Hl3]; simpl.
  clear; generalize dependent l3; generalize dependent l2;
  induction l1; intros l2 l3.
  - reflexivity.
  - destruct l2, l3; try reflexivity.
    simpl. f_equal.
    + apply andb_orb_distrib_l.
    + trivial.
Qed.

Lemma wand_wor_distrib_r : forall {n : nat} (w1 w2 w3 : word n),
  w1 & (w2 | w3) == w1 & w2 | w1 & w3.
Proof.
  intros ? w1 w2 w3;
  destruct w1 as [l1 Hl1], w2 as [l2 Hl2], w3 as [l3 Hl3]; simpl.
  clear; generalize dependent l3; generalize dependent l2;
  induction l1; intros l2 l3.
  - reflexivity.
  - destruct l2, l3; try reflexivity.
    simpl. f_equal.
    + apply andb_orb_distrib_r.
    + trivial.
Qed.

Lemma wnot_wfalse : forall n : nat, ~wfalse n == wtrue n.
Proof.
  intro n; induction n.
  - reflexivity.
  - simpl. f_equal. assumption.
Qed.

Lemma wnot_wtrue : forall n : nat, ~wtrue n == wfalse n.
Proof.
  intro n; induction n.
  - reflexivity.
  - simpl. f_equal. assumption.
Qed.

Lemma wand_wfalse_l : forall {n : nat} (w : word n), wfalse n & w == wfalse n.
Proof.
  intros ? w; destruct w as [l Hl]; subst; simpl; induction l.
  - reflexivity.
  - simpl. f_equal. assumption.
Qed.

Lemma wand_wfalse_r : forall {n : nat} (w : word n), w & wfalse n == wfalse n.
Proof.
  intros ? w; destruct w as [l Hl]; subst; simpl; induction l.
  - reflexivity.
  - simpl. f_equal.
    + apply andb_false_r.
    + assumption.
Qed.

Lemma wand_wtrue_l : forall {n : nat} (w : word n), wtrue n & w == w.
Proof.
  intros ? w; destruct w as [l Hl]; subst; simpl; induction l.
  - reflexivity.
  - simpl. f_equal. assumption.
Qed.

Lemma wand_wtrue_r : forall {n : nat} (w : word n), w & wtrue n == w.
Proof.
  intros ? w; destruct w as [l Hl]; subst; simpl; induction l.
  - reflexivity.
  - simpl. f_equal.
    + apply andb_true_r.
    + assumption.
Qed.

Lemma wor_wtrue_l : forall {n : nat} (w : word n), wtrue n | w == wtrue n.
Proof.
  intros ? w; destruct w as [l Hl]; subst; simpl; induction l.
  - reflexivity.
  - simpl. f_equal. assumption.
Qed.

Lemma wor_wtrue_r : forall {n : nat} (w : word n), w | wtrue n == wtrue n.
Proof.
  intros ? w; destruct w as [l Hl]; subst; simpl; induction l.
  - reflexivity.
  - simpl. f_equal.
    + apply orb_true_r.
    + assumption.
Qed.

Lemma wor_wfalse_l : forall {n : nat} (w : word n), wfalse n | w == w.
Proof.
  intros ? w; destruct w as [l Hl]; subst; simpl; induction l.
  - reflexivity.
  - simpl. f_equal. assumption.
Qed.

Lemma wor_wfalse_r : forall {n : nat} (w : word n), w | wfalse n == w.
Proof.
  intros ? w; destruct w as [l Hl]; subst; simpl; induction l.
  - reflexivity.
  - simpl. f_equal.
    + apply orb_false_r.
    + assumption.
Qed.

Lemma wor_wfalse_intro : forall {n : nat} (w1 w2 : word n),
  w1 == wfalse n -> w2 == wfalse n -> w1 | w2 == wfalse n.
Proof.
  intros ? ? ? H1 H2. rewrite H1. rewrite H2. apply wor_wfalse_l.
Qed.

Lemma wand_wfalse_intro1 : forall {n : nat} (w1 w2 : word n),
  w1 == wfalse n -> w1 & w2 == wfalse n.
Proof.
  intros ? ? ? H. rewrite H. apply wand_wfalse_l.
Qed.

Ltac wand_weqf :=
  lazymatch goal with
    |- context [wnot _] => repeat rewrite wand_assoc;
        lazymatch goal with
        | |- ?E & ~?W == _ =>
              lazymatch E with
              | W => apply wand_wnot_r
              | ?E' & W => rewrite <- (wand_assoc E' W (~W));
                           rewrite (wand_wnot_r W);
                           apply wand_wfalse_r
              | context [W & _] =>
                  lazymatch E with
                    ?E1 & ?E2 => rewrite (wand_comm E1 E2); wand_weqf
                  end
              | context [_ & W] =>
                  lazymatch E with
                    ?E1 & ?E2 => rewrite (wand_comm E1 E2); wand_weqf
                  end
              | _ => apply wand_wfalse_intro1; wand_weqf
              end
        | |- ?E & ?W == _ => rewrite (wand_comm E W); wand_weqf
        end
  end.

Ltac weq_bool :=
  intros; apply weq_iff;
  repeat (rewrite wnot_involutive || rewrite wnot_wor || rewrite wnot_wand);
  repeat (rewrite wand_wor_distrib_l || rewrite wand_wor_distrib_r);
  try rewrite wnot_wfalse; try rewrite wnot_wtrue;
  repeat (rewrite wand_wfalse_l || rewrite wand_wfalse_r);
  repeat (rewrite wand_wtrue_l || rewrite wand_wtrue_r);
  repeat (rewrite wor_wtrue_l || rewrite wor_wtrue_r);
  repeat (rewrite wor_wfalse_l || rewrite wor_wfalse_r);
  split; repeat apply wor_wfalse_intro; try reflexivity; try wand_weqf.

(******************************************************************************)

(************************************shift*************************************)

Lemma wand_1_wshl : forall {n : nat} (w1 w2 : word n),
  ~ (w1 == w2) -> ((wof_N n 1) << w1) & ((wof_N n 1) << w2) == wfalse n.
Proof.
  intros ? w1 w2 H. rewrite weq_iff_Neq in H.
  rewrite <- Nnat.N2Nat.inj_iff in H.
  destruct n as [| n'].
  - reflexivity.
  - change (blist andb
      (firstn (S n') (((list_bool_of_N n' 0) # nil~1) #
                      nat_iter (N.to_nat (wto_N w1)) (cons false) nil))
      (firstn (S n') (((list_bool_of_N n' 0) # nil~1) #
                      nat_iter (N.to_nat (wto_N w2)) (cons false) nil)) =
      nat_iter (S n') (cons false) nil).
    rewrite blist_firstn. rewrite NPeano.Nat.min_id. rewrite wof_N_0.
    apply not_eq in H; destruct H.
    + rewrite (app_assoc (nat_iter (N.to_nat (wto_N w1)) (cons false) nil)).
      replace (N.to_nat (wto_N w2))
      with (S (N.to_nat (wto_N w1)) +
            (N.to_nat (wto_N w2) - S (N.to_nat (wto_N w1))))%nat by omega.
      rewrite iter_cons_split.
      rewrite <- (app_assoc (nat_iter (S (N.to_nat (wto_N w1)))
                                      (cons false) nil)).
      rewrite blist_app. Focus 2.
        rewrite app_length. repeat rewrite length_iter_cons. simpl; omega.
      rewrite blist_andb_falsen_l. rewrite blist_andb_falsen_r.
      rewrite <- iter_cons_split. rewrite firstn_iter_cons. f_equal.
      apply min_l. repeat rewrite app_length. repeat rewrite length_iter_cons.
      repeat rewrite min_l; simpl; omega.
    + rewrite (app_assoc (nat_iter (N.to_nat (wto_N w2)) (cons false) nil)).
      replace (N.to_nat (wto_N w1))
      with (S (N.to_nat (wto_N w2)) +
            (N.to_nat (wto_N w1) - S (N.to_nat (wto_N w2))))%nat by omega.
      rewrite iter_cons_split.
      rewrite <- (app_assoc (nat_iter (S (N.to_nat (wto_N w2)))
                                      (cons false) nil)).
      rewrite blist_app. Focus 2.
        rewrite app_length. repeat rewrite length_iter_cons. simpl; omega.
      rewrite blist_andb_falsen_l. rewrite blist_andb_falsen_r.
      rewrite <- iter_cons_split. rewrite firstn_iter_cons. f_equal.
      apply min_l. repeat rewrite app_length. repeat rewrite length_iter_cons.
      repeat rewrite min_r; simpl; omega.
Qed.

Ltac wand_1_wshl_weqf w1 w2 :=
  lazymatch goal with
    |- context [(wof_N _ 1) << w2] => repeat rewrite wand_assoc;
        lazymatch goal with
        | |- ?E & ((wof_N _ 1) << w2) == _ =>
              lazymatch E with
              | (wof_N _ 1) << w1 => apply wand_1_wshl
              | ?E' & ((wof_N _ 1) << w1) => rewrite <- (wand_assoc E' _ _);
                                             rewrite (wand_1_wshl w1 w2);
                                             try apply wand_wfalse_r
              | context [((wof_N _ 1) << w1) & _] =>
                  lazymatch E with
                    ?E1 & ?E2 => rewrite (wand_comm E1 E2);
                                 wand_1_wshl_weqf w1 w2
                  end
              | context [_ & ((wof_N _ 1) << w1)] =>
                  lazymatch E with
                    ?E1 & ?E2 => rewrite (wand_comm E1 E2);
                                 wand_1_wshl_weqf w1 w2
                  end
              end
        | |- ?E & ?W == _ => rewrite (wand_comm E W); wand_1_wshl_weqf w1 w2
        end
  end.

(******************************************************************************)

(*************************************ring*************************************)

Lemma wadd_0_l : forall {n : nat} (w : word n), wfalse n + w == w.
Proof.
  unfold wadd. intros. rewrite wto_N_wfalse. apply wto_N_id.
Qed.

Lemma wadd_sym : forall {n : nat} (w1 w2 : word n), w1 + w2 == w2 + w1.
Proof.
  unfold wadd. intros. rewrite N.add_comm. reflexivity.
Qed.

Lemma wadd_assoc : forall {n : nat} (w1 w2 w3 : word n),
  w1 + (w2 + w3) == w1 + w2 + w3.
Proof.
  unfold wadd. intros. apply wof_N_weq. repeat rewrite wof_N_mod.
  rewrite N.add_mod_idemp_l; try discriminate.
  rewrite N.add_mod_idemp_r; try discriminate.
  rewrite N.add_assoc. reflexivity.
Qed.

Lemma wmul_1_l : forall {n : nat} (w : word n), (wof_N n 1) * w == w.
Proof.
  unfold wmul. intros n w. rewrite wof_N_mod.
  destruct n as [| n'].
  - destruct w as [l Hl]. destruct l; reflexivity || discriminate.
  - rewrite N.mod_1_l; try reflexivity. rewrite N.mul_1_l. apply wto_N_id.
Qed.

Lemma wmul_sym : forall {n : nat} (w1 w2 : word n), w1 * w2 == w2 * w1.
Proof.
  unfold wmul. intros. rewrite N.mul_comm. reflexivity.
Qed.

Lemma wmul_assoc : forall {n : nat} (w1 w2 w3 : word n),
  w1 * (w2 * w3) == w1 * w2 * w3.
Proof.
  unfold wmul. intros. apply wof_N_weq. repeat rewrite wof_N_mod.
  rewrite N.mul_mod_idemp_l; try discriminate.
  rewrite N.mul_mod_idemp_r; try discriminate.
  rewrite N.mul_assoc. reflexivity.
Qed.

Lemma wdistr_l : forall {n : nat} (w1 w2 w3 : word n),
  (w1 + w2) * w3 == w1 * w3 + w2 * w3.
Proof.
  unfold wadd, wmul. intros. apply wof_N_weq. repeat rewrite wof_N_mod.
  rewrite N.mul_mod_idemp_l; try discriminate.
  rewrite <- N.add_mod; try discriminate.
  rewrite N.mul_add_distr_r. reflexivity.
Qed.

Lemma wsub_def : forall {n : nat} (w1 w2 : word n), w1 - w2 == w1 + (- w2).
Proof.
  reflexivity.
Qed.

Lemma wopp_def : forall {n : nat} (w : word n), w + (- w) == wfalse n.
Proof.
  unfold wopp, wadd. intros ? w. rewrite wof_N_mod. apply wof_N_weq.
  rewrite wto_N_wfalse. rewrite N.add_mod_idemp_r; try discriminate.
  replace (wto_N w + N.succ (wto_N (~ w)))%N with (N.pos (shift_nat n 1)).
  - apply N.mod_same. discriminate.
  - destruct w as [l Hl]; subst; simpl; induction l as [| h t IHt].
    + reflexivity.
    + destruct h; simpl.
      * rewrite N.succ_double_spec. rewrite <- N.add_assoc.
        rewrite <- N.add_1_l. rewrite (N.add_assoc 1).
        change (1 + 1)%N with (2 * 1)%N. repeat rewrite <- N.mul_add_distr_l.
        rewrite N.add_1_l. rewrite <- IHt. reflexivity.
      * rewrite N.succ_double_spec. rewrite <- N.add_1_r.
        rewrite <- (N.add_assoc _ 1). change (1 + 1)%N with (2 * 1)%N.
        rewrite N.double_spec. repeat rewrite <- N.mul_add_distr_l.
        rewrite N.add_1_r. rewrite <- IHt. reflexivity.
Qed.

Module Type Word.
  Parameter n : nat.
End Word.

Module RingWord (Import W : Word).
Add Ring word_ring : (mk_rt (wfalse n) _ _ _ _ _ _
  wadd_0_l wadd_sym wadd_assoc
  wmul_1_l wmul_sym wmul_assoc
  wdistr_l wsub_def wopp_def).
End RingWord.

(******************************************************************************)
