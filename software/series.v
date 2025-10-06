Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import finfun tuple ssralg matrix mxalgebra bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section series.

Lemma powersum1 (n : nat) : 2 * (\sum_(0<=i<n.+1) i) = n * (n.+1). 
Proof.
elim : n.
  by rewrite mul0n big_nat1 muln0.
move => n IH.
rewrite big_nat_recr mulnDr IH.
ring. 
Qed.


Lemma powersum2 (n : nat) : 6 * (\sum_(0<=i<n.+1) i^2) = n * (n.+1) * ((2*n).+1). 
Proof.
elim : n.
  by rewrite mul0n big_nat1 muln0.
move => n IH.
rewrite big_nat_recr mulnDr IH /=. 
ring. 
Qed.

Lemma powersum3 (n : nat) : 4 * (\sum_(0<=i<n.+1) i^3) = n^4 + 2*(n^3) + n^2. 
Proof.
elim : n.
  by rewrite !exp0n // muln0 !addn0 big_nat1 muln0.
move => n IH.
rewrite big_nat_recr mulnDr IH /=. 
ring. 
Qed.

Lemma oddpowersum1 (n : nat) : \sum_(0<=i< 2*n | odd i) i = n^2.
Proof.
elim : n.
  rewrite exp0n // /index_iota subn0 big1_seq //. 
  by move => i; move/andP => [_ H2]; move : H2; rewrite muln0 in_nil. 
move => n.
rewrite !big_mkcond => IH. 
rewrite big_mkcond. rewrite -[n.+1]addn1 mulnDr muln1 addn2 !big_nat_recr IH.
have -> : (odd (2 * n)) = false by rewrite odd_mul.  
have -> : odd (2 * n).+1 by rewrite -addn1 odd_add odd_mul .
rewrite //=. 
ring. 
Qed.

Lemma oddpowersum2 (n : nat) : n + 3 * (\sum_(0<=i< 2*n | odd i) i^2) = 4*(n^3).
Proof.
elim : n.
  rewrite exp0n // /index_iota subn0 big1_seq //. 
  by move => i; move/andP => [_ H2]; move : H2; rewrite muln0 in_nil. 
move => n.
rewrite !big_mkcond => IH. 
rewrite big_mkcond. rewrite -[n.+1]addn1 mulnDr muln1 addn2 !big_nat_recr. 
have -> : (odd (2 * n)) = false by rewrite odd_mul.  
have -> : odd (2 * n).+1 by rewrite -addn1 odd_add odd_mul .
rewrite //= addn0 mulnDr [n + 1]addnC -addnA [n + (_ + _)]addnA IH.
ring.
Qed.

Lemma oddpowersum3 (n : nat) : n^2 +  (\sum_(0<=i< 2*n | odd i) i^3) = 2*(n^4).
Proof.
elim : n.
  rewrite exp0n // /index_iota subn0 big1_seq //. 
  by move => i; move/andP => [_ H2]; move : H2; rewrite muln0 in_nil. 
move => n.


rewrite !big_mkcond => IH. 
rewrite big_mkcond. rewrite -[n.+1]addn1 mulnDr muln1 addn2 !big_nat_recr. 
have -> : (odd (2 * n)) = false by rewrite odd_mul.  
have -> : odd (2 * n).+1 by rewrite -addn1 odd_add odd_mul .
rewrite //= addn0.  
have -> : (n + 1) ^ 2 = 1 + 2 * n + n ^ 2 by ring.
rewrite -addnA [n ^ 2 + (_ + _)]addnA IH.
ring.
Qed.


Lemma series1 (n a d: nat) : 2 * (\sum_(0<=i<n.+1) (a + i * d)) = n.+1 * (2 * a + n * d).
Proof.
elim : n.
  by rewrite big_nat1 mul0n !addn0 mul1n.
move => n IH.
rewrite big_nat_recr [2 * (_ + _)]mulnDr IH. 
ring.
Qed.

Variable (R : comUnitRingType).

Variable x : nat -> R.
Open Local Scope ring_scope.

Lemma subr_sub (m n p : R) : m - n - p = m - (n + p).
Proof.
apply/eqP.
by rewrite !GRing.subr_eq -GRing.addrA [p+n]GRing.addrC GRing.subrK.
Qed.

Import GRing.Theory.

Lemma addrAB (m n p : R):  m + (n - p) = m + n - p.
Proof.
by rewrite addrA.
Qed.



Lemma telescope n : \sum_(0<= i < n.+1) ((x i.+1) - (x i)) = x n.+1 - x 0. 
Proof.
elim : n => [|n _].
  by rewrite big_nat1. 
rewrite sumrB big_nat_recr (@big_nat_recl _ _ _ n.+1) [x 0 + _]addrC
        [(GRing.add_monoid R) (\big[GRing.add_monoid R/0]_(0 <= i < n.+1) x i.+1)
          (x n.+2)]addrC -subr_sub -!addrA [_ + (_ - x 0)]addrA.
move : (eq_refl (\sum_(0 <= i < n.+1) x i.+1));
rewrite -GRing.subr_eq0;
move/eqP => ->.
by rewrite GRing.sub0r.
Qed.



Variable c : nat -> nat -> R.

(* a is beta_p^{i,j-1} - beta_p^{i,j} *)

Definition a (i j : nat) := c i j.-1 - c i j.

Definition b (i j : nat) :=
match i with
| 0 => 0%R
| S n => a n j
end.


Lemma lemma1 (k l p : nat) :
   \sum_(0<=i<k.+1) (\sum_(l.+1 <= j <p) ((a i j) - (b i j))) = \sum_(l.+1<=j<p) (a k j).
Proof.
have H : forall i, (fun _ => true) i  -> (fun i => \sum_(l.+1 <= j < p) (a i j - b i j)) i = 
         (fun i => \sum_(l.+1 <= j < p) (a i j) - \sum_(l.+1 <= j < p) (b i j)) i.
 by move => H1 /=; rewrite GRing.Theory.sumrB.
have -> : \sum_(0 <= i < k.+1) \sum_(l.+1 <= j < p) (a i j - b i j) =
          \sum_(i <- (iota 0 k.+1)) \sum_(l.+1 <= j < p) (a i j - b i j)
 by rewrite /index_iota subn0.
rewrite (@eq_bigr R 0%R _ _ _ (fun _ => true)
      (fun i => \sum_(l.+1 <= j < p) (a i j - b i j))
      (fun i => \sum_(l.+1 <= j < p) (a i j) - \sum_(l.+1 <= j < p) (b i j))
      H).
rewrite GRing.Theory.sumrB.
rewrite (@big_nat_recl _ _ _ _ (fun i => (\sum_(l.+1 <= j < p) b i j))).
rewrite /b (@big1 _ _ _ _ _ _ (fun _ : nat => 0)) // GRing.add0r.
rewrite big_nat_recr.
have -> : (\big[GRing.add_monoid R/0]_(0 <= i < k) (\sum_(l.+1 <= j < p) a i j)) = 
   \sum_(0 <= i < k) \sum_(l.+1 <= j < p) a i j by done.
have -> : (GRing.add_monoid R) (\sum_(0 <= i < k) \sum_(l.+1 <= j < p) a i j)
     (\sum_(l.+1 <= j < p) a k j) =
          (\sum_(l.+1 <= j < p) a k j) + (\sum_(0 <= i < k) \sum_(l.+1 <= j < p) a i j)
  by rewrite GRing.Theory.addrC.
rewrite -GRing.Theory.addrA.
have H1 : \sum_(0 <= i < k) \sum_(l.+1 <= j < p) a i j == \sum_(0 <= i < k) \sum_(l.+1 <= j < p) a i j 
  by done.
rewrite -GRing.subr_eq0 in H1.
by rewrite (eqP H1) GRing.addr0.
Qed.

Lemma lemma2_aux (k l p : nat) (H : l < p) :
  \sum_(l<=j<p) ((c k j.-1) - (c k j)) = (c k l.-1) - (c k p.-1).
Proof.
rewrite GRing.Theory.sumrB big_ltn // (@big_add1 _ _ _ _ _ (fun _ => true)).
rewrite -{2 3}[l]add0n !big_addn.
have [r H1] : exists r, (p - l)%N = r.+1
  by exists (p - l).-1; rewrite -subn_gt0 in H; rewrite (ltn_predK H).
rewrite H1 big_nat_recr.
have -> :  (GRing.add_monoid R)
     (\big[GRing.add_monoid R/0]_(0 <= i < r) c k (i + l))
     (c k (r + l)) = \sum_(0<=i<r) (c k (i+l)) + (c k (r + l)) by done.
have H3 : l <= p by rewrite leq_eqVlt; apply/orP; right.
have -> : r = (p - l).-1%N.
  by rewrite H1 -pred_Sn. 
rewrite -GRing.addrA -subr_sub.
have -> : (p.-1 - l)%N = (p - l).-1.
  by rewrite -subn1 -subnDA addnC addn1 subnS.
have H4 : \sum_(0 <= i < (p - l).-1) c k (i + l) == 
          \sum_(0 <= i < (p - l).-1) c k (i + l)
  by done.
rewrite -GRing.subr_eq0 in H4; rewrite (eqP H4) GRing.sub0r.
have -> : ((p - l).-1 + l)%N = p.-1.
  by rewrite -subnS addnC addnBA -addn1 ?subnDl ?subn1 ?addn1.
by [].
Qed.

Lemma lemma2 (k l p : nat) (H : l < p) :
  \sum_(l.+1<=j<p.+1) ((c k j.-1) - (c k j)) = (c k l) - (c k p).
Proof.
have H1 : l.+1 < p.+1 by done. 
by rewrite (lemma2_aux _ H1) -!pred_Sn.
Qed.

Lemma lemma2' (k l p : nat) (H : l = p) :
  \sum_(l.+1<=j<p.+1) ((c k j.-1) - (c k j)) = (c k l) - (c k p).
Proof.
rewrite H.
move : (eq_refl (c k p)); rewrite -GRing.subr_eq0; move/eqP => ->. 
rewrite /index_iota /=.
have : p.+1 <= p.+1 by done.
by rewrite -subn_eq0; move/eqP => -> /=; rewrite big_nil. 
Qed.

Lemma lemma3 (k l p : nat) (H : l <= p) :
  \sum_(0<=i<k.+1) (\sum_(l.+1 <= j <p.+1) ((a i j) - (b i j))) =
  (c k l) - (c k p).
Proof.
move : H; rewrite leq_eqVlt; move/orP => [H|H].
  by move : H; move/eqP => H; rewrite lemma1 /a lemma2'.
by rewrite lemma1 /a lemma2. 
Qed.






Section invmx.

Import GRing.Theory.
Local Open Scope ring_scope.



Lemma invmx_left : forall m (M M' : 'M[R]_m), M *m M' = 1%:M -> M' *m M = 1%:M.
Proof.
move=> m M M' H.
have hM : (M \in unitmx) by case: (mulmx1_unit H).
have h' : (M' = invmx M) by rewrite -(mulKmx hM M') H mulmx1.
by rewrite h' mulVmx.
Qed.

Lemma invmx_uniq m (M M' : 'M[R]_m) :
  M *m M' = 1%:M -> M' = invmx M.
Proof.
move=> H.
have hM : (M \in unitmx) by case: (mulmx1_unit H).
by rewrite -[M']mulmx1 -(mulmxV hM) mulmxA (invmx_left H) mul1mx.
Qed.

End invmx.

Section pot_matrix.

Import GRing.Theory.
Local Open Scope ring_scope.

Variable (n : nat). 

Fixpoint pot_matrix (M : 'M[R]_n) (m : nat) : 'M[R]_n :=
match m with
| 0 => 1%:M
| S p => M *m (pot_matrix M p)
end.

Lemma pot_1 (i : nat) (M : 'M[R]_n) : 
   (pot_matrix M i *m M) =  (pot_matrix M i.+1).
Proof.
elim : i; first by rewrite mul1mx /pot_matrix mulmx1. 
move => n0 IH; rewrite {1}/pot_matrix -/pot_matrix.
by rewrite -mulmxA IH.
Qed.

End pot_matrix.

Section canonical_matrix.

Open Scope ring_scope.

Variables (n : nat).

Canonical matrix_monoid :=
  Monoid.Law (@mulmxA R n n n n) (@mul1mx R n n) (@mulmx1 R n n).
Canonical matrix_muloid :=
  Monoid.MulLaw (@mul0mx R n n n) (@mulmx0 R n n n).
Canonical matrix_addoid := 
  Monoid.AddLaw (@mulmxDl R n n n) (@mulmxDr R n n n).


End canonical_matrix.


Section inverse_nilpotent.

Open Scope ring_scope.

Variables (n : nat).

Lemma submx_sub (n0 : nat) (m1 n1 p1 : 'M[R]_n0) :
 m1 - n1 - p1 = m1 - (n1 + p1).
Proof.
apply/eqP.
by rewrite !GRing.subr_eq -GRing.addrA [p1+n1]GRing.addrC GRing.subrK.
Qed.

Lemma inverse_I_minus_M : forall (M : 'M[R]_n), 
 (exists m, pot_matrix M m = 0) -> exists N, N *m (1%:M - M) = 1%:M.
Proof.
case : n; first by exists 0; rewrite !thinmx0.
move => n0 M [m].
case : m.
 rewrite /pot_matrix => H.
 have : (@determinant R n0.+1 1%:M) = (@determinant R n0.+1 0) by rewrite H. rewrite det1 det0 => H1; move : (@GRing.oner_neq0 R).
 by rewrite H1; move/eqP.
move => n1.
exists (\sum_(0<=i<n1.+1) (pot_matrix M i)).
rewrite (@big_distrl _ 0 _ (@matrix_addoid n0.+1)).
have -> : \big[matrix_addoid n0.+1/0]_(0 <= i < n1.+1)
        (matrix_muloid n0.+1) (pot_matrix M i) (1%:M - M) =
      \big[matrix_addoid n0.+1/0]_(0 <= i < n1.+1)
        ((pot_matrix M i) *m (1%:M - M)) by done.
have H : forall i : nat , (fun _ => true) i ->
   (fun i => (pot_matrix M i *m (1%:M - M))) i =
   (fun i => ((pot_matrix M i) - ((pot_matrix M i) *m M))) i
  by move => i;
    rewrite [(pot_matrix M i) *m (1%:M - M)]mulmxBr mulmx1.
rewrite (@eq_bigr _ _ _ _ _ _ _ _ H).  
clear H.
rewrite GRing.Theory.sumrB.
have H : forall i : nat , (fun _ => true) i ->
   (fun i => (pot_matrix M i *m M)) i =
   (fun i => (pot_matrix M i.+1)) i.
 by move => i _; rewrite pot_1.
rewrite (@eq_bigr _ _ _ _ _ _ _ _ H) big_nat_recl big_nat_recr
        -GRing.addrA.  
have -> :
  (GRing.add_monoid (matrix_zmodType R n0.+1 n0.+1))
     (\big[GRing.add_monoid (matrix_zmodType R n0.+1 n0.+1)/0]_(0 <= i < n1)
          pot_matrix M i.+1) (pot_matrix M n1.+1) =
  (\big[GRing.add_monoid (matrix_zmodType R n0.+1 n0.+1)/0]_(0 <= i < n1)
          pot_matrix M i.+1) + (pot_matrix M n1.+1) by done.
rewrite -submx_sub.
have H1 : \big[+%R/0]_(0 <= i < n1) pot_matrix M i.+1 == 
   \big[GRing.add_monoid (matrix_zmodType R n0.+1 n0.+1)/0]_(0 <= i < n1)
       pot_matrix M i.+1 by done.
rewrite -GRing.subr_eq0 in H1.
by rewrite (eqP H1) GRing.sub0r {1}/pot_matrix p GRing.subr0.
Qed.


Lemma inverse_I_minus_M' : forall (M : 'M[R]_n), 
 (exists m, pot_matrix M m = 0) -> exists N, (1%:M - M) *m N = 1%:M.
Proof.
move => M H; move : (inverse_I_minus_M H) => [N eH].
exists N.
by rewrite (invmx_left eH).
Qed. 




Variable m : nat.
Variable (M : 'M[R]_n).
Hypothesis nilpotency_m : (pot_matrix M m = 0).

Lemma inverse_I_minus_M_big : 
   (\sum_(0<=i<m) (pot_matrix M i)) *m (1%:M - M) = 1%:M.
Proof.
move : M nilpotency_m.
case : n; first by move => M0 nilpotency_m0; rewrite !thinmx0. 
move => n0 M0.
case : m.
 rewrite /pot_matrix => H.
 have : (@determinant R n0.+1 1%:M) = (@determinant R n0.+1 0) by rewrite H. rewrite det1 det0 => H1; move : (@GRing.oner_neq0 R).
 by rewrite H1; move/eqP.
move => n1 H1.




rewrite (@big_distrl _ 0 _ (@matrix_addoid  n0.+1)).
have -> : \big[matrix_addoid n0.+1/0]_(0 <= i < n1.+1)
        (matrix_muloid n0.+1) (pot_matrix M0 i) (1%:M - M0) =
      \big[matrix_addoid n0.+1/0]_(0 <= i < n1.+1)
        ((pot_matrix M0 i) *m (1%:M - M0)) by done.

have H : forall i : nat , (fun _ => true) i ->
   (fun i => (pot_matrix M0 i *m (1%:M - M0))) i =
   (fun i => ((pot_matrix M0 i) - ((pot_matrix M0 i) *m M0))) i.
  by move => i;
    rewrite [(pot_matrix M0 i) *m (1%:M - M0)]mulmxBr mulmx1.
rewrite (@eq_bigr _ _ _ _ _ _ _ _ H).  
clear H.
rewrite GRing.Theory.sumrB.
have H : forall i : nat , (fun _ => true) i ->
   (fun i => (pot_matrix M0 i *m M0)) i =
   (fun i => (pot_matrix M0 i.+1)) i.
 by move => i _; rewrite pot_1.
rewrite (@eq_bigr _ _ _ _ _ _ _ _ H) big_nat_recl big_nat_recr
        -GRing.addrA.  
have -> :
  (GRing.add_monoid (matrix_zmodType R n0.+1 n0.+1))
     (\big[GRing.add_monoid (matrix_zmodType R n0.+1 n0.+1)/0]_(0 <= i < n1)
          pot_matrix M0 i.+1) (pot_matrix M0 n1.+1) =
  (\big[GRing.add_monoid (matrix_zmodType R n0.+1 n0.+1)/0]_(0 <= i < n1)
          pot_matrix M0 i.+1) + (pot_matrix M0 n1.+1) by done.
rewrite -submx_sub.
have HH1 : \big[+%R/0]_(0 <= i < n1) pot_matrix M0 i.+1 == 
   \big[GRing.add_monoid (matrix_zmodType R n0.+1 n0.+1)/0]_(0 <= i < n1)
       pot_matrix M0 i.+1 by done.
rewrite -GRing.subr_eq0 in HH1.
by rewrite (eqP HH1) GRing.sub0r {1}/pot_matrix H1 GRing.subr0.
Qed.


