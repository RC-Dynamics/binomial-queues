Require Import Coq.Strings.String.
Open Scope nat_scope.
Open Scope list_scope.

(************************************************************************)
(* Copyright 2018 Nilson de Lima, Walber de Macedo, Orlando Neto        *)
(* MIT License                                                          *)
(************************************************************************)

(* As funções e provas já estão em ordem de execução*)

(* Uma lista de prioridade (priqueue), é um tipo de dados que visa simplificar as operações de junção de duas ávores ordenadas. Essa priq é uma lista de árvores que deve obedecer os requisitos:

    1- A lista não deve ter seus elementos com tamanho igual. Cada posição da lista corresponde a uma altura diferente de uma árvore.

    2- As árvores precisam ser uma power of 2 heap (pow2heap). Essa power of 2 heap é apenas uma árvore ordenada como max heap e sua raiz tem seu filho a direita uma árvore vazia, e seu filho a esquerda uma árvore completa. Isso faz com que as árvores tenham uma altura máxima de n. Olhando para a priqueue, temos que para cada índice da lista é o numero n da árvore: a posição 0 da arvore deve ter uma árvore de altura 0 e assim por diante.

   Essa definição facilita a inserção e junção de duas priqueue, fazendo com que a junção seja reduzida a junção de árvores binárias, resultando em um algoritmo parecido com uma soma binária, onde caso uma posição da lista exceda o seu valor máximo de elementos, toda essa árvore seja passada para a próxima posição e tente ser encaixada nessa nova árvore.
*)

(* Representação simplificada de a maior que ou igual a b para ser usada *)

Notation "a >? b" := (Nat.ltb b a)
                     (at level 70, only parsing) : nat_scope.
 
Definition key := nat.

(* Uma árvore é definida como para uma chave, existem duas subárvores onde uma folha não 
   possui chave nem subárvores *)

Inductive tree : Type :=
| Node: key -> tree -> tree -> tree
| Leaf : tree.

Definition priqueue := list tree.

Definition empty : priqueue := nil.

(* Um smash representa a junção de duas árvores, fazendo sempre a ordenação ser preservada *)

Definition smash (t u: tree) : tree :=
  match t , u with
  | Node x t1 Leaf, Node y u1 Leaf =>
                   if x >? y then Node x (Node y u1 t1) Leaf
                                else Node y (Node x t1 u1) Leaf
  | _ , _ => Leaf
  end.

(* Carry é a fase em que uma árvore não pode ficar mais em sua posição atual por ter excedido o tamanho máximo, então ela é passada para a próxima posição sendo somada à próxima árvore. Isso é feito recursivamente até que a árvore resultante tenha tamanho suficiente para ser acomodada naquela posição. *)

Fixpoint carry (q: list tree) (t: tree) : list tree :=
  match q, t with
  | nil, Leaf => nil
  | nil, _ => t :: nil
  | Leaf :: q', _ => t :: q'
  | u :: q', Leaf => u :: q'
  | u :: q', _ => Leaf :: carry q' (smash t u)
 end.

(* Um insert é apenas uma inserção em uma priqueue, o novo numero é colocado na primeira árvore e é visto
   se a árvore resultante pode ser encaixada nessa posição, utilizando o carry. *)

Definition insert (x: key) (q: priqueue) : priqueue :=
     carry q (Node x Leaf Leaf).


(*  *)

Fixpoint unzip (t: tree) (cont: priqueue -> priqueue) : priqueue :=
  match t with
  | Node x t1 t2 => unzip t2 (fun q => Node x t1 Leaf :: cont q)
  | Leaf => cont nil
  end.

Compute (unzip (Node 9
          (Node 4 (Node 3 (Node 1 Leaf Leaf) (Node 1 Leaf Leaf))
             (Node 3 (Node 2 Leaf Leaf) (Node 5 Leaf Leaf)))
          (Node 5 (Node 3 (Node 2 Leaf Leaf) (Node 2 Leaf Leaf))
             (Node 3 (Node 1 Leaf Leaf) (Node 1 Leaf Leaf)))) (fun u => u)).

(* Definição para a função de remoção do valor máximo de uma max heap.  *)

Definition heap_delete_max (t: tree) : priqueue :=
  match t with
  | Node x t1 Leaf => unzip t1 (fun u => u)
  | _ => nil
  end.

Compute (heap_delete_max (Node 9
          (Node 4 (Node 3 (Node 1 Leaf Leaf) (Node 1 Leaf Leaf))
             (Node 3 (Node 2 Leaf Leaf) (Node 5 Leaf Leaf))) Leaf)).

(* Find max retorna o valor máximo em uma priqueue. *)

Fixpoint find_max' (current: key) (q: priqueue) : key :=
  match q with
  | nil => current
  | Leaf :: q' => find_max' current q'
  | Node y _ _ :: q' => find_max' (if current >? y then current else y) q'
  end.

Fixpoint find_max (q: priqueue) : option key :=
  match q with
  | nil => None
  | Leaf :: q' => find_max q'
  | Node x _ _ :: q' => Some (find_max' x q')
  end.

Compute (find_max (Node 1 Leaf Leaf
       :: Node 3 (Node 1 Leaf Leaf) Leaf
          :: Node 5 (Node 3 (Node 2 Leaf Leaf) (Node 2 Leaf Leaf)) Leaf
             :: Node 9
                  (Node 4 (Node 3 (Node 1 Leaf Leaf) (Node 1 Leaf Leaf))
                     (Node 3 (Node 2 Leaf Leaf) (Node 5 Leaf Leaf))) Leaf
                :: nil)).

(*  *)

Fixpoint join (p q: priqueue) (t: tree) : priqueue :=
  match p, q, t with
  | nil, _, _ => carry q t
  | _, nil, _ => carry p t
  | Leaf :: p', Leaf :: q', _ => t :: join p' q' Leaf
  | Leaf :: p', q1 :: q', Leaf => q1 :: join p' q' Leaf
  | Leaf :: p', q1 :: q', Node _ _ _ => Leaf :: join p' q' (smash t q1)
  | p1 :: p', Leaf :: q', Leaf => p1 :: join p' q' Leaf
  | p1 :: p', Leaf :: q', Node _ _ _ => Leaf :: join p' q' (smash t p1)
  | p1 :: p', q1 :: q', _ => t :: join p' q' (smash p1 q1)
  end.
  
(*  *)

 Fixpoint delete_max_aux (m: key) (p: priqueue) : priqueue * priqueue :=
  match p with
  | Leaf :: p' => let (j,k) := delete_max_aux m p' in (Leaf::j, k)
  | Node x t1 Leaf :: p' =>
       if m >? x
       then (let (j,k) := delete_max_aux m p'
             in (Node x t1 Leaf::j,k))
       else (Leaf::p', heap_delete_max (Node x t1 Leaf))
  | _ => (nil, nil)
  end.

Definition delete_max (q: priqueue) : option (key * priqueue) :=
  match find_max q with
  | None => None
  | Some m => let (p',q') := delete_max_aux m q
                            in Some (m, join p' q' Leaf)
  end.

(* Para facilitar a utilização do join, é criada uma função auxiliar chamada merge. *)

Definition merge (p q: priqueue) := join p q Leaf.

(* Essa função diz se uma árvore é uma pow2heap, ela verifica se o nó raiz tem uma subárvore vazia a direita e se possui uma subárvore completa a esquerda. *)

Fixpoint pow2heap' (n: nat) (m: key) (t: tree) :=
 match n, m, t with
    0, m, Leaf => True
  | 0, m, Node _ _ _=> False
  | S _, m,Leaf => False
  | S n', m, Node k l r =>
       (m >= k) /\ pow2heap' n' k l /\ pow2heap' n' m r
 end.

Definition pow2heap (n: nat) (t: tree) :=
  match t with
  | Node m t1 Leaf => pow2heap' n m t1
  | _ => False
  end.

(* Para saber se realmente uma lista de árvores é uma priqueue, temos que garantir que cada árvore seja uma pow2heap de tamanho único, assim a cada nova árvore avaliada na lista, o tamanho é incrementado e verificado se é uma pow2heap daquele tamanho. *)

Fixpoint priq' (i: nat) (l: list tree) : Prop :=
   match l with
  | t :: l'=> (t = Leaf \/ pow2heap i t) /\ priq' (S i) l'
  | nil => True
 end.

Definition priq (q: priqueue) : Prop := priq' 0 q.

(* A prova de uma priqueue vazia é trivial, já que foi definida que uma lista vazia é uma priqueue. *)

Theorem empty_priq : priq empty.
Proof. reflexivity. Qed.

(* Para provar que uma junção de duas pow2heap de tamanho n é valida, é necessário checar se a junção das duas leva a uma pow2heap de tamanho n+1. Isso é feito tomando os casos base de cada árvore e checando se de fato a propriedade da max heap é satisfeita. *)

Theorem smash_valid : forall (n: nat) (t: tree) (u: tree),
  pow2heap n t -> pow2heap n u -> pow2heap (S n) (smash t u).
Proof.
  intros. destruct t, u.
    - destruct t2, u2.
      + simpl in H. inversion H.
      + simpl in H. inversion H.
      + simpl in H0. inversion H0.
      + unfold smash. destruct (Nat.ltb k0 k) as []eqn:?.
        * simpl. intuition. Search (_ >= _).
          apply Compare_dec.not_lt. Search (~ _ < _).
          apply PeanoNat.Nat.lt_asymm. apply PeanoNat.Nat.ltb_lt. apply Heqb.
        * simpl. intuition. apply Compare_dec.not_lt.
          apply PeanoNat.Nat.ltb_nlt. apply Heqb.
   - inversion H0.
   - inversion H.
   - inversion H.
Qed.

(* Um carry é valido para toda a priqueue q de tamanho n, para uma árvore t sendo pow2heap ou uma árvore vazia, o resultado do carry é uma priqueue de tamanho n. Isso é feito aplicando uma indução em q e sempre reduzindo t para casos conhecidos, tudo feito sem necessariamente saber, induzir ou destruir o tamanho (n) das priqueues. *)

Theorem carry_valid : forall (n: nat) (q: priqueue),
  priq' n q -> forall (t: tree), (t = Leaf \/ pow2heap n t) ->
  priq' n (carry q t).
Proof.
  intros n q. revert n. induction q.
    - intros. destruct t.
      + unfold carry. simpl. split.
        * apply H0.
        * reflexivity.
      + simpl. reflexivity.
    - intros. destruct a, t.
      + unfold carry. fold carry. unfold priq'. split.
        * left. reflexivity.
        * fold priq'. apply IHq.
          { inversion H. apply H2. }
          { right. apply smash_valid.
            { intuition.
              { inversion H1. } }
            { inversion H. inversion H1.
              { inversion H3. }
              { apply H3. } } }
      + unfold carry. apply H.
      + unfold carry. simpl. split.
        * apply H0.
        * inversion H. apply H2.
      + simpl. split.
        * left. reflexivity.
        * inversion H. apply H2.
Qed.

(* Ao fazer uma inserção de um natural em uma priqueue q, ela deve continuar sendo uma priqueue. A prova deve ser feita utilizando o caso base de uma priqueue vazia, e ao ser feita a inserção numa árvore, pode ser utilizada a prova carry_valid. *)

Theorem insert_priq : forall (x: nat) (q: priqueue),
  priq q -> priq (insert x q).
Proof.
  intros. destruct q.
  - unfold priq. simpl. split.
    + right. apply I.
    + apply I.
  - inversion H. unfold insert. apply carry_valid.
    + simpl. split.
      * apply H0.
      * apply H1.
    + simpl. intuition.
Qed.

(*  *)

Theorem join_valid: forall (p: priqueue) (q: priqueue) (n: nat) (c: tree),
  priq' n p -> priq' n q -> (c = Leaf \/ pow2heap n c) -> priq' n (join p q c).
Proof.
  induction p.
    - intros. destruct q, c.
      + simpl. split.
        * apply H1.
        * apply I.
      + simpl. apply I.
      + unfold join. apply carry_valid.
        * apply H0.
        * apply H1.
      + unfold join. apply carry_valid.
        * apply H0.
        * apply H1.
    - intros. destruct a, q, c.
      + unfold join. apply carry_valid.
        * apply H.
        * apply H1.
      + unfold join. unfold carry. apply H.
      + unfold join. fold join. destruct t.
        * unfold priq'. split.
          { apply H1. }
          { fold priq'. apply IHp.
            { inversion H. apply H3. }
            { inversion H0. apply H3. }
            { right. apply smash_valid.
              { inversion H. inversion H2.
                { inversion H4. }
                { apply H4. } }
              { inversion H0. inversion H2.
                { inversion H4. }
                { apply H4. } } } }
        * unfold priq'. split.
          { left. reflexivity. }
          { fold priq'. apply IHp.
            { inversion H. apply H3. }
            { inversion H0. apply H3. }
            { right. apply smash_valid.
              { inversion H1.
                { inversion H2. }
                { apply H2. } }
              { inversion H. inversion H2.
                { inversion H4. }
                { apply H4. } } } }
     + destruct t.
        * unfold join. fold join. unfold priq'. split.
          { apply H1. }
          { fold priq'. apply IHp.
            { inversion H. apply H3. }
            { inversion H0. apply H3. }
            { right. apply smash_valid.
              { inversion H. inversion H2.
                { inversion H4. }
                { apply H4. } }
              { inversion H0. inversion H2.
                { inversion H4. }
                { apply H4. } } } }
        * unfold join. fold join. unfold priq'. split.
          { right. inversion H. inversion H2.
            { inversion H4. }
            { apply H4. } }
          { fold priq'. apply IHp.
            { inversion H. apply H3. }
            { inversion H0. apply H3. }
            { left. reflexivity. } }
    + unfold join. unfold carry. simpl. split.
      * apply H1.
      * inversion H. apply H3.
    + simpl. split.
      * left. reflexivity.
      * inversion H. apply H3.
    + destruct t.
        * unfold join. fold join. unfold priq'. split.
          { left. reflexivity. }
          { fold priq'. apply IHp.
            { inversion H. apply H3. }
            { inversion H0. apply H3. }
            { right. apply smash_valid.
              { inversion H. inversion H2.
                { inversion H4. inversion H1.
                  { inversion H5. }
                  { apply H5. } } 
                { inversion H0. inversion H2.
                { inversion H4. }
                { inversion H4. } } }
            { inversion H0.
              { inversion H2.
                { inversion H4. }
                { apply H4. } } } } }
        * unfold join. fold join. unfold priq'. split.
          { apply H1. }
          { fold priq'. apply IHp.
            { inversion H. apply H3. }
            { inversion H0. apply H3. }
            { left. reflexivity. } }
    + destruct t.
        * unfold join. fold join. unfold priq'. split.
          { right. inversion H0. inversion H2.
             { inversion H4. }
              { apply H4. } }
          { fold priq'. apply IHp.
            { inversion H. apply H3. }
            { inversion H0. apply H3. }
            { left. reflexivity. } }
        * unfold join. fold join. unfold priq'. split.
          { left. reflexivity. }
          { fold priq'. apply IHp.
            { inversion H. apply H3. }
            { inversion H0. apply H3. }
            { left. reflexivity. } }
Qed.

(* Ao fazer um merge entre duas priqueue, o resultado deve ser uma priqueue. Isso é facilmente feito utilizando a prova para o join, já que merge é definido em a partir do join. *)

Theorem merge_priq: forall (p: priqueue) (q: priqueue),
  priq p -> priq q -> priq (merge p q).
Proof.
  intros. unfold merge. apply join_valid; auto.
Qed.