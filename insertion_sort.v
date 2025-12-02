Require Import Arith Lia.
Require Import List.
Import ListNotations.
Require Import Sorted.
Require Import Permutation.

(** * Ordenação por Inserção *)

Fixpoint insert (x:nat) l :=
  match l with
  | [] => [x]
  | h::tl => if (x <=? h)
             then x::l
             else h::(insert x tl)
  end.

Fixpoint insertion_sort (l: list nat) :=
  match l with
  | []  => []
  | h::tl => insert h (insertion_sort tl)
  end.

(** * Lemas Auxiliares *)

(** Lema 1: insert preserva permutação *)
Lemma insert_perm : forall x l,
  Permutation (insert x l) (x :: l).
Proof.
  intros x l.
  induction l as [| h tl IH].
  - simpl. apply Permutation_refl.
  - simpl. destruct (x <=? h) eqn:E.
    + apply Permutation_refl.
    + apply perm_trans with (h :: x :: tl).
      * apply perm_skip. apply IH.
      * apply perm_swap.
Qed.

(** Lema 2: insert mantém lista ordenada *)
Lemma insert_sorted : forall x l,
  Sorted le l -> Sorted le (insert x l).
Proof.
  intros x l H.
  induction H as [| a | a b l' Hab Hsorted IH].
  - simpl. apply Sorted_cons.
    + constructor.
    + constructor.
  - simpl. destruct (x <=? a) eqn:E.
    + apply Leb_complete in E.
      apply Sorted_cons.
      * apply Sorted_cons; constructor.
      * apply HdRel_cons. assumption.
    + apply Sorted_cons.
      * apply Sorted_cons; constructor.
      * apply HdRel_cons.
        apply leb_complete_conv in E.
        lia.
  - simpl. destruct (x <=? a) eqn:E.
    + apply Leb_complete in E.
      apply Sorted_cons.
      * apply Sorted_cons; assumption.
      * apply HdRel_cons. assumption.
    + simpl in IH.
      destruct (x <=? b) eqn:E2.
      * apply Leb_complete in E2.
        apply Sorted_cons.
        { apply Sorted_cons; assumption. }
        { apply HdRel_cons. assumption. }
      * apply Sorted_cons.
        { apply IH. }
        { apply HdRel_cons. assumption. }
Qed.


(** Lema 3: insertion_sort produz permutação *)
Lemma insertion_sort_perm : forall l,
  Permutation (insertion_sort l) l.
Proof.
  intros l.
  induction l as [| h tl IH].
  - simpl. apply Permutation_refl.
  - simpl.
    apply perm_trans with (h :: insertion_sort tl).
    + apply insert_perm.
    + apply perm_skip. apply IH.
Qed.

(** Lema 4: insertion_sort produz lista ordenada *)
Lemma insertion_sort_sorted : forall l,
  Sorted le (insertion_sort l).
Proof.
  intros l.
  induction l as [| h tl IH].
  - simpl. constructor.
  - simpl. apply insert_sorted. apply IH.
Qed.

(** * Teorema Principal *)
Theorem insertion_sort_correct: forall l,
  Sorted le (insertion_sort l) /\ Permutation (insertion_sort l) l.
Proof.
  intros l.
  split.
  - apply insertion_sort_sorted.
  - apply insertion_sort_perm.
Qed.
