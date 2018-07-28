import data.finset

lemma fin_1_ss {n : ℕ} (H : n = 1) : ∀ (m₁ m₂ : fin n), m₁ = m₂ := sorry
lemma finset_card_1 : ∀ {X : Type} [decidable_eq X] (s : finset X), s.card = 1 → ∀ {x₁ x₂ : X}, x₁ ∈ s → x₂ ∈ s → x₁ = x₂ :=

section island

-- the number of people on the island
parameter (N : ℕ)

@[reducible] def person := fin N
@[reducible] def timestep := ℕ

parameter knows (t : timestep) (n : person) (p : Prop) : Prop

def common_knowledge (t : timestep) (p : Prop) : ℕ → Prop
| 0     := ∀ (n : person), knows t n p
| (d+1) := ∀ (n : person), knows t n (common_knowledge d)

variable knows_forall : ∀ {t : timestep} {n : person} {X : Type} {p : X → Prop}, knows t n (∀ x, p x) → ∀ x, knows t n (p x)
-- TODO(dselsam): variable knows_exists, might not be possible to avoid logical omniscience

parameter marked_ones : finset (fin N)

def is_marked (n : person) : Prop := n ∈ marked_ones

variable initial_sight₁   : ∀ (n m : person), n ≠ m → is_marked m → knows 0 n (is_marked m)
variable initial_sight₂   : ∀ (n m : person), n ≠ m → ¬ is_marked m → knows 0 n (¬ is_marked m)

variable initial_oracle  : common_knowledge 1 (∃ m, is_marked m) N

variable no_one_leaves   : ∀ (n : person) (t : timestep), t < N → ¬ knows t n (is_marked n)
variable beliefs_persist : ∀ {t : timestep} {n : person} {p : Prop}, knows t n p → knows (t+1) n p

lemma common_knowledge_loosen {t : timestep} {p : Prop} {d₁ d₂ : ℕ} :
  d₂ < d₁ → common_knowledge t p d₁ → common_knowledge t p d₂ := sorry

theorem base_case_M : marked_ones.card = 1 → ∀ (n : person), is_marked n → knows 1 n (is_marked n) :=
assume (H_card : marked_ones.card = 1) (n : person) (H_n : is_marked n),

have H₂ : common_knowledge 1 (∃ m, is_marked m) N, from initial_oracle,
have H₃ : common_knowledge 1 (∃ m, is_marked m) 0, from common_knowledge_loosen sorry H₂,

have H₃ : knows 1 n (∃ m, is_marked m),
  begin simp only [common_knowledge] at H₃, exact H₃ n end,

begin

end
/-
have H₅ : knows 0 n ((is_marked n ∧ marked_ones.card = M) ∨ (¬ is_marked n ∧ marked_ones.card + 1 = M)),
  from initial_sight n,

have H₆ : knows 1 n ((is_marked n ∧ marked_ones.card = M) ∨ (¬ is_marked n ∧ marked_ones.card + 1 = M)),
  from beliefs_persist H₅,

have H₅ : (M > 0) → ((is_marked n ∧ marked_ones.card = M) ∨ (¬ is_marked n ∧ marked_ones.card + 1 = M)) → is_marked n,
  begin
  intros H_M_gt_0 H_marked_or,
  cases H_marked_or with H_and H_and,
  exact H_and.left,
  cases H_and with H_not_marked H_card,
  end,


show knows 1 n (is_marked n), from logical_omniscience H₄ H₅

-/
end island
