(*
    CoMoEx, Rocq Practice. Covered topics: Various Inductive Principles. Running Example: Eveness of Natural Numbers.
    Copyright (C) 2026  Max Ole Elliger

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *)
From Stdlib Require Import
  Bool
  Nat
  .

(**
   Some notes regarding this file:
   - Lemma [plus_n_Sm] might be helpful.
   - Sometimes, the use of [assert] or [enough] (both behave similar in a way) might be helpful in order to strengthen a proof goal.
 *)

(** * Different Definitions of Eveness *)

Definition even1 (n : nat) : Prop :=
  exists k, n = 2 * k.

Arguments even1 n /.

Example even1_10 :
  even1 10.
Proof.
Admitted.

Lemma even1_double :
  forall n,
    even1 (2 * n).
Proof.
Admitted.

Fixpoint even2 (n : nat) : bool :=
  match n with
  | 0 => true
  | S n' =>
      match n' with
      | 0 => false
      | S n'' => even2 n''
      end
  end.

Example even2_10 :
  even2 10 = true.
Proof.
Admitted.

Lemma even2_double :
  forall n,
    even2 (2 * n) = true.
Proof.
  (* Lemma [plus_n_Sm] might be helpful. *)
Admitted.

Fixpoint even3 (n : nat) : bool :=
  match n with
  | 0 => true
  | S n' => odd3 n'
  end
  with odd3 (n : nat) : bool :=
  match n with
  | 0 => false
  | S n' => even3 n'
  end.

Example even3_10 :
  even3 10 = true.
Proof.
Admitted.

Lemma even3_double :
  forall n,
    even3 (2 * n) = true.
Proof.
  (* Lemma [plus_n_Sm] might be helpful. *)
  Admitted.

Inductive even4 : nat -> Prop :=
  | even4_I_0 :
      even4 0
  | even4_I_SS :
      forall n,
        even4 n ->
        even4 (S (S n)).

Example even4_of_10 :
  even4 10.
Proof.
Admitted.

Lemma even4_double :
  forall n,
    even4 (2 * n).
Proof.
Admitted.

Inductive even5 : nat -> Prop :=
  | even5_I_0 :
      even5 0
  | even5_I_S :
      forall n,
        odd5 n ->
        even5 (S n)
  with odd5 : nat -> Prop :=
  | odd5_S :
      forall n,
        even5 n ->
        odd5 (S n).

Example even5_10 :
  even1 10.
Proof.
Admitted.

Lemma even5_double :
  forall n,
    even5 (2 * n).
Proof.
  induction n as [|n' IH].
  -
    constructor.
  -
    simpl.
    rewrite <- plus_n_Sm.
    do 2 constructor.
    exact IH.
Qed.

(** * Various Helpful Induction Schemes *)

(**
   We prove a custom induction scheme for natural numbers that allows us to take two steps in each inductive case.
 *)
Lemma nat_ind_two_steps :
  forall (P : nat -> Prop),
    P 0 ->
    P 1 ->
    (forall n, P n -> P (S (S n))) ->
    forall n,
      P n.
Proof.
  intros * H1 H2 H3.
  enough (forall n, P n /\ P (S n)) by firstorder.
  induction n as [|n' IH]; firstorder.
Qed.

(**
   This command generates the mutual induction scheme for [even5] and [odd5].
 *)
Scheme even5_ind_odd5 := Induction for even5 Sort Prop
  with odd5_ind_even5 := Induction for odd5 Sort Prop.

Check even5_ind_odd5.

(**
   Here is an example how to use alternative induction principles.
 *)
Goal forall (P : nat -> Prop) (P0 : nat -> Prop) (n : nat),
  even5 n -> P n.
Proof.
  intros P P0.
  Fail induction 1 as [|n H1 IH1|n H1 IH1] using even5_ind_odd5.
  induction 1 as [|n H1 IH1|n H1 IH1] using even5_ind_odd5 with (P0 := fun n _ => P0 n).
  Show 1.
  Show 2.
  Show 3.
Abort.

(** * Equivalence of Definitions

   Constraint: You may use the lemma [nat_ind_two_steps] in at most two of the following theorems!
 *)

Theorem even1_even2 :
  forall n,
    even1 n -> even2 n = true.
Proof.
Admitted.

Theorem even2_even3 :
  forall n,
    even2 n = true ->
    even3 n = true.
Proof.
Admitted.

Theorem even3_even4 :
  forall n,
    even3 n = true -> even4 n.
Proof.
Admitted.

Theorem even4_even5 :
  forall n,
    even4 n -> even5 n.
Proof.
Admitted.

Theorem even5_even1 :
  forall n,
    even5 n -> even1 n.
Proof.
Admitted.

(** * Some Examples regarding [inversion] *)

Example even4_of_5 :
  ~ even4 5.
Proof.
  intro.
  repeat match goal with
         | [H : even4 _ |- _] => inversion H; subst; clear H
         end.

  Restart. (* TODO "Unfold" this automised proof in order to understand what inversion does! *)

Admitted.
