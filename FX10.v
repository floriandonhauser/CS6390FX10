Require Import ZArith.

Inductive expression : Type :=
| constant (c : Z) : expression
| a_inc (d : nat) : expression
.


Inductive statement : Type :=
| skip_s : statement
| is (i : instruction) (s : statement) : statement
with
instruction : Type :=
| skip_i : instruction
| a_write (d: nat) (e : expression) : instruction
| while (d : nat) (s: statement) : instruction
| async (s : statement) :instruction
| finish (s : statement) :instruction
| call (i:nat)
.


Inductive program : Type :=
| p_cons (i:nat) (s : list statement)
.


Inductive tree : Type :=
| finished : tree
| sequential (t1 : tree) (t2 : tree) : tree
| parallel (t1 : tree) (t2 : tree) : tree
| exec (s : statement) : tree
.

Definition array := list Z.

Inductive state : Type :=
| cons_state (P : program) (A : array) (T : tree)
.


Fixpoint get_function (i:nat) (p:program) : statement :=
match p with
| p_cons n s =>
(match i,s with
| _,nil => skip_s
| O, cons x l => x
| S i',cons x l => get_function i' (p_cons n l)
end)
end.


Fixpoint init (p:program) : state:=
  match p with
    | p_cons i s=> cons_state p nil (exec (get_function i p))
  end.

Fixpoint get_from_array (a:array) (i:nat) :Z :=
match i,a with
|_,nil => 0
|O,cons x l => x
| S i', cons x l => get_from_array l i'
end.

Fixpoint eval_expr (a:array) (e:expression) : Z:=
match e with
| constant z => z
| a_inc d => (get_from_array a d)+1
end.

Fixpoint write_to_array (a:array) (i:nat) (val:Z):array:=
match i,a with
|O,nil => cons val nil
|S i',nil => cons  Z0 (write_to_array nil i' val)
|O,cons x l => cons val l
| S i', cons x l => cons x (write_to_array l i' val)
end.


Fixpoint get_state_tuple (p:program) : state:=
match p with
| p_cons i l=>cons_state p nil (exec (get_function i p))
end.

Fixpoint dot (s1:statement) (s2:statement) : statement :=
  match s1 with
    | is i s => is i (dot s s2)
    | skip_s => s2
  end
.


Inductive stepsto : state -> state -> Prop :=
| step_1 p A T2 : stepsto (cons_state p A (sequential finished T2)) (cons_state p A T2) 
| step_2 p A A' T1 T1' T2 : (stepsto (cons_state p A T1) (cons_state p A' T1'))
-> (stepsto (cons_state p A (sequential T1 T2)) (cons_state p A' (sequential T1' T2)))
| step_3 p A T2 : stepsto (cons_state p A (parallel finished T2)) (cons_state p A T2)
| step_4 p A T1 : stepsto (cons_state p A (parallel T1 finished)) (cons_state p A T1)
| step_5 p A A' T1 T1' T2 : (stepsto (cons_state p A T1) (cons_state p A' T1'))
-> (stepsto (cons_state p A (parallel T1 T2)) (cons_state p A' (parallel T1' T2)))
| step_6 p A A' T1 T2 T2': (stepsto (cons_state p A T2) (cons_state p A' T2'))
-> (stepsto (cons_state p A (parallel T1 T2)) (cons_state p A' (parallel T1 T2')))
| step_7 p A : stepsto (cons_state p A (exec skip_s)) (cons_state p A finished)
| step_8 p A k : stepsto (cons_state p A (exec(is skip_i k))) (cons_state p A (exec k))
| step_9 p A d e k : stepsto (cons_state p A (exec(is (a_write d e) k))) (cons_state p (write_to_array A d (eval_expr A e)) (exec k))
| step_10 p A d s k : ((get_from_array A d)=Z0)->stepsto (cons_state p A (exec (is (while d s) k))) (cons_state p A (exec k))
| step_11 p A d s k : ((get_from_array A d)<>Z0)->stepsto (cons_state p A (exec (is (while d s) k))) (cons_state p A (exec (dot s (is (while d s) k))))
| step_12 p A s k : stepsto (cons_state p A (exec (is (async s) k))) (cons_state p A (parallel (exec s) (exec k)))
| step_13 p A s k : stepsto (cons_state p A (exec (is (finish s) k))) (cons_state p A (sequential (exec s ) (exec  k))) 
| step_14 p A i k : stepsto (cons_state p A (exec((is (call i) k)))) (cons_state p A (exec (dot (get_function i p) k)))
.



Inductive stepsto_star : state -> state -> Prop :=
| zerotimes (s : state) : stepsto_star s s
| atleastonce (s1 s2 s3 : state) : stepsto s1 s2
-> stepsto_star s2 s3 -> stepsto_star s1 s3
.

Definition empty_p := (cons_state (p_cons 0 nil) nil finished).

Example nothing: stepsto_star empty_p empty_p.
Proof.
apply zerotimes. Qed.

Example add_1 : stepsto_star (cons_state (p_cons 0 (cons (is (a_write 0 (constant 42)) skip_s) nil)) (cons Z0 nil) (exec (is (a_write 0 (constant 42)) skip_s)))
(cons_state (p_cons 0 (cons (is (a_write 0 (constant 42)) skip_s) nil)) (cons (Z.of_nat 42) nil) finished).
Proof.

apply atleastonce with ((cons_state (p_cons 0 (cons (is (a_write 0 (constant 42)) skip_s) nil)) (cons (Z.of_nat 42) nil) (exec skip_s))).
-apply step_9.
-apply atleastonce with(  (cons_state (p_cons 0 (is (a_write 0 (constant 42)) skip_s :: nil))
     (Z.of_nat 42 :: nil)%list finished)). 
      +apply step_7.
      +apply zerotimes.
Qed.


Inductive value : state -> Prop :=
  finished_value (p:program) (a:array) : value (cons_state p a finished)
.


Theorem p_stays_same: forall (p1 p2 :program) (a1 a2 : array) (t1 t2 :tree),
  stepsto (cons_state p1 a1 t1) (cons_state p2 a2 t2) -> p1 = p2.
Proof.
  intros. inversion H; reflexivity.
Qed.

Theorem progress: forall (s:state), value s \/ exists s', stepsto s s'.
Proof.
  intros s. induction s. induction T. (* induction on the tree structure *) 
  - (* Proves finished part *) left. apply finished_value.
  - (* Proves sequential part *) right. destruct IHT1.
    + (* T1 is a value *) exists (cons_state P A T2). inversion H. apply step_1.
    + (* T1 can step *) inversion H. destruct x as [P' A' T1']. 
      exists (cons_state P A' (sequential T1' T2)).
      apply step_2. assert(H1 := H0). apply p_stays_same in H0. rewrite <- H0 in H1. apply H1.
  - (* Proves parallel part *) right. destruct IHT1.
    + (* T1 is a value *) exists (cons_state P A T2). inversion H. apply step_3.
    + (* T1 can step *) inversion H. destruct x as [P' A' T1']. 
      exists (cons_state P A' (parallel T1' T2)).
      apply step_5. assert(H1 := H0). apply p_stays_same in H0. rewrite <- H0 in H1. apply H1.
  - (* Proves exec part *) right. destruct s.
    + (* no instruction left *) exists (cons_state P A finished). apply step_7.
    + (* instructions left *) destruct i. (* case distinction on the instruction *) 
      * (* skip_i *) exists (cons_state P A (exec s)). apply step_8.
      * (* a_write *) exists (cons_state P (write_to_array A d (eval_expr A e)) (exec s)). apply step_9.
      * (* while *) remember (Z.eqb (get_from_array A d) Z0) as read. destruct read.
        {(* end of while loop *) exists (cons_state P A (exec s)). apply step_10.
          destruct (get_from_array A d). {reflexivity. } {inversion Heqread. }
          {inversion Heqread. }}
        {(* continue while loop *) exists (cons_state P A (exec (dot s0 (is (while d s0) s)))).
          apply step_11. destruct (get_from_array A d). {inversion Heqread. }
          {discriminate. } {discriminate. }}
      * (* async *) exists (cons_state P A (parallel (exec s0) (exec s))). apply step_12.
      * (* finish *) exists (cons_state P A (sequential (exec s0 ) (exec  s))). apply step_13.
      * (* call *) exists (cons_state P A (exec (dot (get_function i P) s))). apply step_14.
Qed.




