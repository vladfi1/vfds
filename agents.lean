import data.finset
import data.fintype

-- theory of mind
def timestep := ℕ

namespace tom

@[reducible] def beliefs := set Prop

def is_logical (bs : beliefs) : Prop := ∀ {p q : Prop}, p ∈ bs → (p → q) ∈ bs → q ∈ bs
def is_omniscient (bs : beliefs) : Prop := ∀ {p : Prop}, p → p ∈ bs

/-
theorem is_logical_implies_is_conjunctive : ∀ (bs : beliefs), is_logical bs → is_conjunctive bs :=
assume (bs : beliefs) (H_log : is_logical bs),
show is_conjunctive bs, from
have H₁ : ∀ (p q : Prop), p ∈ bs → (p → q) → q ∈ bs, from @H_log,
show ∀ (p q : Prop), p ∈ bs → q ∈ bs → p ∧ q ∈ bs, from
assume (p q : Prop) (H_p : p ∈ bs) (H_q : q ∈ bs),
show p ∧ q ∈ bs, from
have H₂ : p → (q → (p ∧ q)), from sorry,
let H₃ := H₁ _ _ H_p H₂ in
let H₄ := H₁ _ _ H₃ H_q in
begin
end
-/

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

-- knows a1 (knows a2 (b = ff) ∨ knows a2 (b = tt))
-- is_correct (a : agent) : Prop := ∀ p, knows a p → knows god p

-- knows a1 (knows a2 (b = ff) ∨ knows a2 (b = tt))
-- knows a1 (knows a3 (b = ff) ∨ knows a3 (b = tt))

-- knows a1 ((knows a2 (b = ff) ∧ knows a3 (b = ff)) ∨ (knows a2 (b = tt) ∧ knows a3 (b = tt)))

--def all_know_and_agree_on_value (agents : set agent) (V : Type) [fintype V] :
-- knows a1 (OR_{values : type-in-question} (AND_{a : agents} (knows a (b = values))))

axiom all_agents_logical (agent : set agent) : ∀ (a : agent),










end tom
