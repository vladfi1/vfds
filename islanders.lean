import data.finset

/-
Version 1:
-------------

[Theorem]
Forall n, if n people are marked, then they all leave on the nth day.
[Proof]
By induction.
[base] If no one is marked, they all trivially leave on the 0th day.
[step]
- Suppose if n people are marked, they all leave on the nth day,
- Suppose n+1 people are marked.
- A marked person sees n people marked, and reasons as follows:
  - if they are not marked, there are n people marked, and they would all leave on the nth day.
  - when they don't, he realizes he must be marked, so leaves on the n+1st day.

[Gaps]

-/

section islanders

parameter (n_people : ℕ)
@[reducible] def person := fin n_people
@[reducible] def timestep := ℕ

parameter knows (t : timestep) (n : person) (p : Prop) : Prop

parameter beliefs_persist : ∀ {t : timestep} {n : person} {p : Prop}, knows t n p → knows (t+1) n p

parameters knows_and : ∀ {t : timestep} {n : person} {p q : Prop}, knows t n p → knows t n q → knows t n (p ∧ q)

def common_knowledge (t : timestep) (p : Prop) : ℕ → Prop
| 0     := ∀ (n : person), knows t n p
| (d+1) := ∀ (n : person), knows t n (common_knowledge d)

lemma common_knowledge_loosen {t : timestep} {p : Prop} {d₁ d₂ : ℕ} :
  d₂ < d₁ → common_knowledge t p d₁ → common_knowledge t p d₂ := sorry

parameter logical_omniscience : ∀ {t : timestep} {n : person} {p q : Prop}, knows t n p → (p → q) → knows t n q

parameter marked_ones : finset person
parameter N_seen : person → ℕ

include marked_ones N_seen

def n_marked : ℕ := marked_ones.card
def is_marked (n : person) : Prop := n ∈ marked_ones

parameter holds : Prop → Prop

variable holds_and : ∀ {P Q : Prop}, holds P → holds Q → holds (P ∧ Q)
variable holds_logical : ∀ {P Q : Prop}, holds P → (P → Q) → holds Q
variable holds_contradiction : ¬ holds false

include holds_and holds_logical holds_contradiction

variable initial_sight :
∀ {M : ℕ}, holds (marked_ones.card = M) →
  common_knowledge 0 (∀ (n : person), (is_marked n ∧ N_seen n + 1 = M) ∨ (¬ is_marked n ∧ N_seen n = M)) n_people

variable initial_oracle : common_knowledge 0 (marked_ones.card > 0) n_people

variable no_one_leaves  : ∀ (t : timestep), t < n_marked → common_knowledge t (∀ (n : person), ¬ knows t n (is_marked n)) n_people

theorem islanders : ∀ (M : ℕ), holds (n_marked = M) → ∀ (n : person), holds (is_marked n) → knows M n (is_marked n) :=
begin
intro M,
induction M with M IHM,
{
intros H_holds_card n H_holds_marked,
-- We can derive a contradiction from the following:
--   H_holds_card : holds (n_marked = 0),
--   H_holds_marked : holds (is_marked n)
have H_holds_pre_contradiction : holds (n_marked = 0 ∧ is_marked n), from holds_and H_holds_card H_holds_marked,
have H_holds_false : holds false, from /- holds_logical -/ sorry,
have H_false : false, from holds_contradiction H_holds_false,
exact false.rec _ H_false,
},

intros H_holds_card n H_holds_marked,
-- this is common knowledge at timestep 0
have H_beliefs_all_or : knows (nat.succ M) n (∀ (m : person), (is_marked m ∧ N_seen m + 1 = M) ∨ (¬ is_marked m ∧ N_seen m = M)), from sorry,
-- application of a known fact
have H_beliefs_or : knows (nat.succ M) n ((is_marked n ∧ N_seen n + 1 = M) ∨ (¬ is_marked n ∧ N_seen n = M)), from sorry,
-- since nobody left, n knows that nobody knew they were marked at timestep M
have H_believes_leave : knows (nat.succ M) n (∀ (m : person), ¬ knows M m (is_marked m)), from sorry,
--

end




end islanders
