Require Import Coq.Strings.String.
Open Scope nat_scope.
Open Scope list_scope.

Notation "a >? b" := (Nat.ltb b a)
                     (at level 70, only parsing) : nat_scope.

Definition key := nat.

Inductive tree : Type :=
| Node: key -> tree -> tree -> tree
| Leaf : tree.

Definition priqueue := list tree.

Definition empty : priqueue := nil.

Definition smash (t u: tree) : tree :=
  match t , u with
  | Node x t1 Leaf, Node y u1 Leaf =>
                   if x >? y then Node x (Node y u1 t1) Leaf
                                else Node y (Node x t1 u1) Leaf
  | _ , _ => Leaf
  end.

Fixpoint carry (q: list tree) (t: tree) : list tree :=
  match q, t with
  | nil, Leaf => nil
  | nil, _ => t :: nil
  | Leaf :: q', _ => t :: q'
  | u :: q', Leaf => u :: q'
  | u :: q', _ => Leaf :: carry q' (smash t u)
 end.

Definition insert (x: key) (q: priqueue) : priqueue :=
     carry q (Node x Leaf Leaf).

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

Definition heap_delete_max (t: tree) : priqueue :=
  match t with
  | Node x t1 Leaf => unzip t1 (fun u => u)
  | _ => nil
  end.

Compute (heap_delete_max (Node 9
          (Node 4 (Node 3 (Node 1 Leaf Leaf) (Node 1 Leaf Leaf))
             (Node 3 (Node 2 Leaf Leaf) (Node 5 Leaf Leaf))) Leaf)).

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

Definition merge (p q: priqueue) := join p q Leaf.

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

Fixpoint priq' (i: nat) (l: list tree) : Prop :=
   match l with
  | t :: l'=> (t = Leaf \/ pow2heap i t) /\ priq' (S i) l'
  | nil => True
 end.

Definition priq (q: priqueue) : Prop := priq' 0 q.


