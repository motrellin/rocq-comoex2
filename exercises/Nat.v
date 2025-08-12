
(** * Natural Numbers

   We define the type of natural numbers as an abstract datatype via the constructors [zero] and [succ].
 *)

Inductive nat : Type :=
  | zero : nat
  | succ : nat -> nat.

(**
   We can build abstract terms from this definition:
 *)

Example one : nat := succ zero.

Example two : nat
  (* TODO Remove the following line and add a suitable definition! *)
  . Admitted.

Goal two = succ one.
Proof.
Admitted.

(** * Addition

   Addition is a function that takes two arguments of type [nat] and returns a [nat]ural number.

   We define [add] _recursively_.
 *)

Fixpoint add (n m : nat) : nat :=
  match n with
  | zero => m
  | succ n' => succ (add n' m)
  end.

Example one_add_one_is_two :
  add one one = two.
Proof.
Admitted.

(**
   The following two facts [add_zero_l] and [add_succ_l] show exactly how [simpl]ification works when the decreasing argument of a recursively defined function is known.
 *)

Fact add_zero_l :
  forall m,
    add zero m = m.
Proof.
  intros m.
  simpl.
  reflexivity.

  Restart.

  intros m.
  reflexivity.

  Restart.

  reflexivity.
Qed.

Fact add_succ_l :
  forall n m,
    add (succ n) m = succ (add n m).
Proof.
Admitted.

(**
   We _inductively_ prove associativity of [add].
 *)

Theorem add_assoc : 
  forall n m o,
    add n (add m o) = add (add n m) o.
Proof.
  intros n m o.
  induction n as [|n' IH].
  Show 2. (* Shows the proof state of the second proof goal. *)
  -
    simpl.
    reflexivity.
  -
    simpl.
    rewrite IH.
    reflexivity.

  Restart.

  induction n as [|n' IH].
  all: intros m o.
  -
    reflexivity.
  -
    simpl.
    rewrite IH with
      (m := m)
      (o := o).

    Undo.

    rewrite IH.
    reflexivity.
Qed.

(**
   We try to proceed in a similar way in order to prove commutativity of [add].
 *)

Theorem add_comm :
  forall n m,
    add n m = add m n.
Proof.
  induction n as [|n' IH].
  -
    intros m.
    simpl.
    Fail reflexivity.
    (* TODO Explain the failure *)
Abort.

(**
   We extract the missing property to an extra lemma in order to reuse it in future.
*)

Lemma add_zero_r :
  forall n,
    add n zero = n.
Proof.
Admitted.

Theorem add_comm :
  forall n m,
    add n m = add m n.
Proof.
  induction n as [|n' IH].
  -
    intros m.
    simpl.
    rewrite add_zero_r.
    reflexivity.
  -
    intros m.
    simpl.
    rewrite IH.
    Fail reflexivity.
    (* TODO Explain the failure *)
Abort.

(* TODO Add another lemma which might be needed to finally prove [add_comm]! *)

Theorem add_comm :
  forall n m,
    add n m = add m n.
Proof.
Admitted.

(** ** Alternative Definitions *)

Module add_alternative_currying.

  Check add.
  Print add.

  (**
     We present a slightly changed version of [add]:
   *)

  Fixpoint add' (n : nat) : nat -> nat :=
    match n with
    | zero => fun m => m
    | succ n' => fun m => succ (add' n' m)
    end.

  (*
     TODO Describe the difference between [add'] and [add]!
  *)

  Proposition add'_eq_add :
    add' = add.
  Proof.
    unfold add'.
    unfold add.
  Abort. (* TODO Why do we abort this proof.? *)

  Proposition add'_eq_ext_add :
    forall n m,
      add' n m = add n m.
  Proof.
  Admitted.

  (**
     When we defined [nat], the fold principle [nat_rect] was automatically defined.
   *)

  Check nat_rect.

  (**
     This principle capsulates the recursion principle.
     Therefore, observer that the following definition is not defined using the keyword [Fixpoint]:
   *)
     
  Definition add'' : nat -> nat -> nat :=
    nat_rect (fun _ => nat -> nat)
    (fun m => m)
    (fun n' r m => succ (r m)).

  Proposition add''_eq_add' :
    add'' = add'.
  Proof.
    reflexivity.
  Qed.

End add_alternative_currying.

Module add_alternative_implementation.

  Fixpoint add' (n m : nat) : nat :=
    match n with
    | zero => m
    | succ n' => add' n' (succ m)
    end.

  Proposition add'_eq_ext_add :
    forall n m,
      add' n m = add n m.
  Proof.
    (*
       TODO Do not use additional lemmas in here which you did not introduce yet!

       You should generalize the inductive hypothesis as much as possible.
     *)
  Admitted.

End add_alternative_implementation.

(** * Multiplication *)

Fixpoint mult (n m : nat) : nat
  (* TODO Remove the following line and add a suitable definition! *)
  . Admitted.
  
Example one_mult_two_is_two :
  mult one two = two.
Proof.
Admitted.

Theorem mult_comm :
  forall n m,
    mult n m = mult m n.
Proof.
Admitted.

Theorem mult_add_distr_1 :
  forall n m o,
    add (mult n m) (mult n o) = mult n (add m o).
Proof.
Admitted.

Theorem mult_add_distr_2 :
  forall n m o,
    add (mult n o) (mult m o) = mult (add n m) o.
Proof.
Admitted.

Theorem mult_assoc :
  forall n m o,
    mult n (mult m o) = mult (mult n m) o.
Proof.
Admitted.
