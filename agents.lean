import data.finset

-- theory of mind
def timestep := ℕ

namespace tom

@[reducible] def beliefs := set Prop

def is_logical (bs : beliefs) : Prop := ∀ {p q : Prop}, p ∈ bs → (p → q) → q ∈ bs
def is_conjunctive (bs : beliefs) : Prop := ∀ {p q : Prop}, p ∈ bs → q ∈ bs → p ∧ q ∈ bs
def is_reflexive (bs : beliefs) : Prop := ∀ {p : Prop}, p ∈ bs ↔ (p ∈ bs) ∈ bs

constant agent : Type
constant god   : agent

constant world  : agent → timestep → beliefs
constant agents : finset agent

def believes (a : agent) (t : timestep) (p : Prop) : Prop := p ∈ world a t
def all_believe (agents : set agent) (t : timestep) (p : Prop) : Prop := ∀ (a : agent), a ∈ agents → believes a t p

def common_knowledge (agents : set agent) (t : timestep) (p : Prop) : ℕ → Prop
| 0     := all_believe agents t p
| (d+1) := common_knowledge d ∧ all_believe agents t (common_knowledge d)

lemma common_knowledge_loosen (agents : set agent) (t : timestep) (p : Prop) (d₁ d₂ : ℕ) :
  d₂ < d₁ → common_knowledge agents t p d₁ → common_knowledge agents t p d₂ := sorry












end tom
