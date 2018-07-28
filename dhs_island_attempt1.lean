lemma fin_1_ss {n : ℕ} (H : n = 1) : ∀ (m₁ m₂ : fin n), m₁ = m₂ := sorry

section tina

parameter (N : ℕ)

@[reducible] def person := fin N
@[reducible] def timestep := ℕ

parameter is_marked : person → Prop
parameter knows (t : timestep) (n : person) (p : Prop) : Prop

def common_knowledge_core (t : timestep) (p : Prop) : ℕ → Prop
| 0     := ∀ (n : person), knows t n p
| (d+1) := ∀ (n : person), knows t n (common_knowledge_core d)

def common_knowledge (t : timestep) (p : Prop) : Prop := common_knowledge_core t p (N-1)

variable logical_omniscience : ∀ {t : timestep} {n : person} {p q : Prop}, knows t n p → (p → q) → knows t n q
variable initial_oracle  : common_knowledge 1 (∃ (m : person), is_marked m)
variable no_one_leaves   : ∀ (n : person) (t : timestep), t < N → ¬ knows t n (is_marked n)
variable beliefs_persist : ∀ {t : timestep} {n : person} {p : Prop}, knows t n p → knows (t+1) n p

/-
TODO(dselsam, vladfi): separate out the number of people on the island from the number of people who are marked.
The proper base case is 1 person is marked, with an arbitrary number of non-marked people.

Note: I think logical omniscience is fine, as long as we don't assert facts that no individual agent knows.
-/

theorem base_case        : N = 1 → ∀ (n : person), knows 1 n (is_marked n) :=
assume H₁ : N = 1,
assume n : person,
have H₂ : common_knowledge 1 (∃ (m : person), is_marked m), from initial_oracle,
have H₃ : ∀ (n : person), knows 1 n (∃ m, is_marked m),
  by simp only [common_knowledge, common_knowledge_core, H₁] at H₂ ; exact H₂,
have H₄ : knows 1 n (∃ m, is_marked m), from H₃ n,
have H₅ : (∃ m, is_marked m) → is_marked n,
  begin intro ex, cases ex with m H_m, rw fin_1_ss H₁ n m, exact H_m end,
show knows 1 n (is_marked n), from logical_omniscience H₄ H₅

end tina
