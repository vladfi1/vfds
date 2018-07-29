import data.finset

lemma fin_1_ss {n : ℕ} (H : n = 1) : ∀ (m₁ m₂ : fin n), m₁ = m₂ := sorry
lemma finset_card_1 : ∀ {X : Type} [decidable_eq X] (s : finset X), s.card = 1 → ∀ {x₁ x₂ : X}, x₁ ∈ s → x₂ ∈ s → x₁ = x₂ := sorry

section island

-- the number of people on the island
parameter (N : ℕ)

@[reducible] def person := fin N
@[reducible] def timestep := ℕ

parameter knows (t : timestep) (n : person) (p : Prop) : Prop

parameter beliefs_persist : ∀ {t : timestep} {n : person} {p : Prop}, knows t n p → knows (t+1) n p

parameters knows_and : ∀ {t : timestep} {n : person} {p q : Prop}, knows t n p → knows t n q → knows t n (p ∧ q)

def common_knowledge (t : timestep) (p : Prop) : ℕ → Prop
| 0     := ∀ (n : person), knows t n p
| (d+1) := ∀ (n : person), knows t n (common_knowledge d)

lemma common_knowledge_loosen {t : timestep} {p : Prop} {d₁ d₂ : ℕ} :
  d₂ < d₁ → common_knowledge t p d₁ → common_knowledge t p d₂ := sorry

parameter all_rational : ∀ {t : timestep} {n : person} {p q : Prop}, knows t n p → (p → q) → knows t n q

parameter marked_ones : finset (fin N)

def is_marked (n : person) : Prop := n ∈ marked_ones

parameter holds : Prop → Prop

parameter initial_sight :
  ∀ {n : person} {M : ℕ},
    holds (marked_ones.card = M) →
    holds (is_marked n)
    → knows 0 n ((is_marked n ∧ marked_ones.card = M) ∨ (¬ is_marked n ∧ marked_ones.card + 1 = M))

parameter initial_oracle  : common_knowledge 1 (marked_ones.card > 0) N

parameter no_one_leaves   : ∀ (n : person) (t : timestep), t < N → ¬ knows t n (is_marked n)

theorem base_case : ∀ (n : person), holds (is_marked n) → holds (marked_ones.card = 1) → knows 1 n (is_marked n) :=
assume (n : person) (H_n : holds (is_marked n)) (H_card : holds (marked_ones.card = 1)),

have H₁ : common_knowledge 1 (marked_ones.card > 0) N, from initial_oracle,
have H₂ : common_knowledge 1 (marked_ones.card > 0) 0, from common_knowledge_loosen sorry H₁,
have H₃ : knows 1 n (marked_ones.card > 0), from H₂ n,
have H₄ : knows 0 n ((is_marked n ∧ marked_ones.card = 1) ∨ (¬ is_marked n ∧ marked_ones.card + 1 = 1)), from initial_sight H_card H_n,
have H₅ : knows 1 n ((is_marked n ∧ marked_ones.card = 1) ∨ (¬ is_marked n ∧ marked_ones.card + 1 = 1)), from beliefs_persist H₄,

have H₆ : marked_ones.card > 0 → ¬ (¬ is_marked n ∧ marked_ones.card + 1 = 1), from sorry, -- split and arith
have H₇ : knows 1 n (¬ (¬ is_marked n ∧ marked_ones.card + 1 = 1)), from all_rational H₃ H₆,
have H₈ : knows 1 n (((is_marked n ∧ marked_ones.card = 1) ∨ (¬ is_marked n ∧ marked_ones.card + 1 = 1)) ∧ (¬ (¬ is_marked n ∧ marked_ones.card + 1 = 1))), from knows_and H₅ H₇,
have H₉ : (((is_marked n ∧ marked_ones.card = 1) ∨ (¬ is_marked n ∧ marked_ones.card + 1 = 1)) ∧ (¬ (¬ is_marked n ∧ marked_ones.card + 1 = 1))) → is_marked n ∧ marked_ones.card = 1, from sorry, -- propositional reasoning

have H_10 : knows 1 n (is_marked n ∧ marked_ones.card = 1), from all_rational H₈ H₉,
have H_11 : (is_marked n ∧ marked_ones.card = 1) → is_marked n, from and.left,
show knows 1 n (is_marked n), from all_rational H_10 H_11

theorem step_case : ∀ (M : ℕ) (n : person) (H_n : holds (is_marked n)),
                      (holds (marked_ones.card = M+1) → knows (M+1) n (is_marked n))
                    → (holds (marked_ones.card = M+2) → knows (M+2) n (is_marked n)) :=
sorry

theorem islanders : ∀ (M : ℕ) (n : person) (H_n : holds (is_marked n)), holds (marked_ones.card = M+1) → knows (M+1) n (is_marked n) :=
begin
intros M,
induction M with M IHm,
apply base_case,
intros n H_n H_card,
apply step_case M n H_n,
intro H_card2,
apply IHm,
exact H_n,
exact H_card2,
exact H_card
end

end island
