import data.finset
import data.fintype

-- theory of mind
def timestep := ℕ

namespace tom

@[reducible] def beliefs := set Prop

def is_logical (bs : beliefs) : Prop := ∀ {p q : Prop}, p ∈ bs → (p → q) ∈ bs → q ∈ bs
def is_reflective (bs : beliefs) : Prop := ∀ {p q : Prop}, p ∈ bs → (p ∈ bs) ∈ bs
def is_conjunctive (bs : beliefs) : Prop := ∀ {p q : Prop}, p ∈ bs → q ∈ bs → (p ∧ q) ∈ bs

constant agent : Type
constant god   : agent

constant world  : agent → timestep → beliefs

def believes (a : agent) (t : timestep) (p : Prop) : Prop := p ∈ world a t
def all_believe (agents : set agent) (t : timestep) (p : Prop) : Prop := ∀ (a : agent), a ∈ agents → believes a t p

def common_knowledge (agents : set agent) (t : timestep) (p : Prop) : ℕ → Prop
| 0     := all_believe agents t p
| (d+1) := common_knowledge d ∧ all_believe agents t (common_knowledge d)

lemma common_knowledge_loosen (agents : set agent) (t : timestep) (p : Prop) (d₁ d₂ : ℕ) :
  d₂ < d₁ → common_knowledge agents t p d₁ → common_knowledge agents t p d₂ := sorry

def all_logical (agents : set agent) := ∀ (a : agent), a ∈ agents → ∀ t, is_logical (world a t)
def all_reflective (agents : set agent) := ∀ (a : agent), a ∈ agents → ∀ t, is_reflective (world a t)
def all_conjunctive (agents : set agent) := ∀ (a : agent), a ∈ agents → ∀ t, is_conjunctive (world a t)

namespace islanders

constant agents : set agent

axiom initial_sight : ∀ (a :

parameter initial_sight :
  ∀ {n : person} {M : ℕ},
    holds (marked_ones.card = M) →
    common_knowledge 0 (∀ (n : person), (is_marked n ∧ N_seen n + 1 = M) ∨ (¬ is_marked n ∧ N_seen n = M)) N

parameter initial_oracle  : common_knowledge 1 (marked_ones.card > 0) N

parameter no_one_leaves   : ∀ (t : timestep), t < N → common_knowledge t (∀ (n : person), ¬ knows t n (is_marked n)) N










end islanders
end tom
