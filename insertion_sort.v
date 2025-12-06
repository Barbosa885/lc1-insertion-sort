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

(** Lema 1: insert preserva permutação 
    Mostra que inserir x em l resulta em uma lista que é permutação de x :: l. *)
Lemma insert_perm : forall x l,
  Permutation (insert x l) (x :: l).
Proof.
  intros x l.
  induction l as [| h tl IH].
  - (* Caso Base: lista vazia *)
    simpl. apply Permutation_refl.
  - (* Caso Indutivo: lista h::tl *)
    simpl. destruct (x <=? h) eqn:E.
    + (* Caso x <= h: insere no início *)
      apply Permutation_refl.
    + (* Caso x > h: insere na cauda *)
      apply perm_trans with (h :: x :: tl).
      * apply perm_skip. apply IH. (* Usa hipótese de indução *)
      * apply perm_swap.
Qed.

(** Lema 2: insert mantém lista ordenada 
    Se a lista l está ordenada, inserir x mantém a ordenação. *)
Lemma insert_sorted : forall x l,
  Sorted le l -> Sorted le (insert x l).
Proof.
  intros x l H.
  (* Indução na estrutura da lista l, não na prova de Sorted *)
  induction l as [| h tl IH].
  - simpl. constructor.
    + constructor.
    + constructor.
  - simpl. destruct (x <=? h) eqn:E.
    + (* Caso x <= h: x entra antes de h *)
      apply Nat.leb_le in E.
      constructor.
      * assumption. (* A lista original já estava ordenada *)
      * constructor. assumption.
    + (* Caso x > h: x entra depois de h *)
      apply Nat.leb_gt in E.
      inversion H; subst. (* Decompoe a prova de que h::tl é ordenada *)
      simpl. constructor.
      * apply IH. assumption. (* Hipótese de indução: insert x tl é ordenada *)
      * (* Precisamos mostrar que h <= cabeça de (insert x tl) *)
        destruct tl.
        { (* tl vazia: insert x [] = [x], e h < x *)
          simpl. constructor. lia. }
        { (* tl não vazia: analisamos onde x entra *)
          simpl. destruct (x <=? n) eqn:E2.
          - (* x entra antes de n: h < x *)
            constructor. lia.
          - (* x entra depois de n: h <= n (da lista original) *)
            constructor. inversion H3. assumption. }
Qed.


(** Lema 3: insertion_sort produz permutação 
    A lista ordenada contém os mesmos elementos da original. *)
Lemma insertion_sort_perm : forall l,
  Permutation (insertion_sort l) l.
Proof.
  intros l.
  induction l as [| h tl IH].
  - simpl. apply Permutation_refl.
  - simpl.
    apply perm_trans with (h :: insertion_sort tl).
    + apply insert_perm. (* Usa Lema 1 *)
    + apply perm_skip. apply IH. (* Hipótese de indução *)
Qed.

(** Lema 4: insertion_sort produz lista ordenada 
    O resultado final é uma lista ordenada. *)
Lemma insertion_sort_sorted : forall l,
  Sorted le (insertion_sort l).
Proof.
  intros l.
  induction l as [| h tl IH].
  - simpl. constructor.
  - simpl. apply insert_sorted. apply IH. (* Usa Lema 2 e Hipótese de Indução *)
Qed.

(** * Teorema Principal 
    Combina os lemas de ordenação e permutação para provar a correção total. *)
Theorem insertion_sort_correct: forall l,
  Sorted le (insertion_sort l) /\ Permutation (insertion_sort l) l.
Proof.
  intros l.
  split.
  - apply insertion_sort_sorted. (* Lema 4 *)
  - apply insertion_sort_perm.   (* Lema 3 *)
Qed.
