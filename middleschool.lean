-- inductive player : Type | a | b | c

open list

#print nat.no_confusion_type
#print nat.no_confusion

def adjacent_pred {α : Type} (p : α -> α -> Prop) : list α -> Prop
| [] := true
| [x] := true
| (x :: y :: tail) := p x y ∧ adjacent_pred (y :: tail)

def allp : list Prop -> Prop
| [] := true
| (x::xs) := x ∧ allp xs

def is_occurrence_list {α : Type} (x : α) (xs : list α) (idxs : list ℕ) : Prop :=
  adjacent_pred nat.lt idxs ∧ allp (list.map (λ n, nth xs n = some x) idxs)

def diff_n (n : nat) := (λ x y, x + n ≤ y)
def increasing_by (n : ℕ) := adjacent_pred (diff_n n)

lemma allp_nth {α : Type} {xs : list α} {f : α -> Prop}
  : allp (list.map f xs) -> forall n (h : n < length xs), f (nth_le xs n h) :=
begin
intro,
induction xs with x xs IHxs,
intros,
cases h,
intros,
cases n with n,
unfold nth_le,
exact a.left,

unfold nth_le,
apply IHxs,
apply a.right
end

lemma adjacent_pred_nth {α : Type} {xs : list α} {p : α -> α -> Prop} :
  (adjacent_pred p xs) <->
  forall n {h1 : n < length xs} {h2 : nat.succ n < length xs},
  p (nth_le xs n h1) (nth_le xs (nat.succ n) h2) :=
begin
apply iff.intro,

intros,
revert xs,
induction n,

intros,
cases xs,
cases h1,
cases xs_tl,
unfold length at h2,
cases h2, cases h2_a,

unfold nth_le,
exact a.left,

intros,
cases xs,
cases h1,

unfold nth_le,
apply n_ih,

cases xs_tl,
cases h1, cases h1_a,
exact a.right,

--backwards
induction xs,
intros,
unfold adjacent_pred,

intros,
cases xs_tl,
unfold adjacent_pred,
unfold adjacent_pred,

split,
apply a 0,
unfold length,
apply nat.zero_lt_succ,

unfold length,
apply nat.succ_lt_succ,
apply nat.zero_lt_succ,

apply xs_ih,
intros,
apply a (nat.succ n),
apply nat.succ_lt_succ,
apply h1,
apply nat.succ_lt_succ,
apply h2,
end

lemma increasing_nth {xs : list ℕ} {k : ℕ} :
  (increasing_by k xs) -> ∀ n (H : n < length xs), (nth_le xs n H) ≥ k * n :=
begin
intros,
induction n,
unfold has_mul.mul nat.mul,
apply nat.zero_le,

unfold has_mul.mul nat.mul,
cases xs,
cases H,

unfold nth_le,
apply le_trans,

apply add_le_add_right,
apply n_ih,
apply nat.lt_of_succ_lt,
assumption,

apply le_trans,
apply adjacent_pred_nth.elim_left a,
assumption,
unfold nth_le,
end

lemma asd {n m : nat} : n ≤ m -> n = m ∨ n < m :=
begin
intro,
cases a,
apply or.inl,
refl,

apply or.inr,
apply nat.succ_le_succ,
apply a_a,
end

lemma some_length {α : Type} {x : α} {n : nat} {xs : list α} : (nth xs n = some x) -> n < length xs :=
begin
revert xs,
induction n,
intro, cases xs,
intro, cases a,

intro,
unfold length,
apply nat.zero_lt_succ,

intros, cases xs,
cases a,

unfold length,
apply nat.succ_lt_succ,
apply n_ih,
apply a,
end

set_option trace.check true

lemma nth_le_nth {α : Type} {x : α} {xs : list α} {n : nat} (h : n < length xs) :
  nth xs n = some x -> nth_le xs n h = x :=
begin
revert xs,
induction n,

intro, cases xs,
intro, cases h,

intros,
unfold nth at a,
unfold nth_le,
cases a, refl,

intros,
cases xs,
cases h,
unfold nth at a,
unfold nth_le,
apply n_ih,
assumption,
end

lemma diff2 {α : Type} (x : α) (xs : list α) (idxs : list ℕ) :
  is_occurrence_list x xs idxs ∧ adjacent_pred ne xs ->
  increasing_by 2 idxs :=
begin
intro, cases a, cases a_left,

apply adjacent_pred_nth.elim_right,

let h_ne := adjacent_pred_nth.elim_left a_right,
let h_lt := adjacent_pred_nth.elim_left a_left_left,
let h_x := allp_nth a_left_right,

intros,
unfold diff_n,

cases asd (@h_lt n h1 h2),

apply absurd (h_ne (nth_le idxs n h1)),
intro, apply a,

simp [h],

rw nth_le_nth _ (h_x n h1),
rw nth_le_nth _ (h_x (nat.succ n) h2),

apply some_length,
apply h_x,
rw h,
apply some_length,
apply h_x,

exact h,
end

lemma le_pred (n : nat) (m : nat) : n ≤ nat.succ m -> nat.pred n ≤ m :=
begin
intro,
cases n,
unfold nat.pred,
apply nat.zero_le,
unfold nat.pred,
apply nat.le_of_succ_le_succ,
assumption,
end

lemma nth_lt {α : Type} {x : α} {xs : list α} {n : nat} : list.nth xs n = option.some x -> n < length xs :=
begin
revert xs,
induction n,

intro,
cases xs,
unfold nth,
intro, cases a,

unfold nth,
intro,
unfold length,
apply nat.zero_lt_succ,

intro,
cases xs,
unfold nth,
intro, cases a,

unfold nth,
intro,
unfold length,
apply nat.succ_lt_succ,
apply n_ih,
assumption
end

theorem main {α : Type} (x : α) (xs : list α) (idxs : list ℕ) :
  is_occurrence_list x xs idxs -> adjacent_pred ne xs -> list.length xs ≥ 2 * list.length idxs - 1 :=
begin
intros,

cases idxs,
simp,
apply nat.zero_le,

let idxs := idxs_hd :: idxs_tl,
let i := length idxs_tl,

have i_le : i < length idxs,

dsimp,
apply nat.lt_succ_self,

let h2 := allp_nth a.right,

have h1 : nth_le idxs i i_le < length xs,
apply nth_lt,
apply h2, clear h2,

unfold length,
unfold has_mul.mul nat.mul,

unfold has_sub.sub nat.sub nat.pred,
apply le_trans,
tactic.swap,
apply h1,
apply nat.succ_le_succ,

apply le_trans, tactic.swap,
apply increasing_nth,
apply diff2,

split,
exact a,
exact a_1,

apply nat.mul_le_mul_left,
apply nat.le_refl,
end

theorem main2 {α : Type} (x : α) (xs : list α) (idxs : list ℕ) :
  is_occurrence_list x xs idxs -> adjacent_pred ne xs -> list.length xs = 2 * list.length idxs - 1 ->
  ∀ n (H : n < length idxs), (nth_le idxs n H) = 2 * n :=
begin
intros,
sorry
end
