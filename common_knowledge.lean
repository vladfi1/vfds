constants p1 p2 : bool

def bool_to_nat : bool -> nat
| ff := 0
| tt := 1

def count (p1 p2 : bool) : nat := bool_to_nat p1 + bool_to_nat p2

inductive person : Type | a | b

def people : list person := [person.a, person.b]

constant color : person -> bool

constant beliefs (p : person) : nat -> set Prop

def is_rational (s : set Prop) : Prop := ∀ (p q : Prop), (p -> q) -> (p ∈ s) -> (q ∈ s)

axiom everyone_rational : ∀ p n, is_rational (beliefs p n)

--axiom initial_beliefs : ∀ p, 

def all_believe (beliefs : set (set Prop)) (p : Prop) : Prop := forall b, b ∈ beliefs -> p ∈ b

def common_knowledge_core (beliefs : set (set Prop)) (p : Prop) : nat -> Prop
| 0 := all_believe beliefs p
| (nat.succ n) := all_believe beliefs (common_knowledge_core n)

def common_knowledge (beliefs : set (set Prop)) (p : Prop) : Prop := forall n, common_knowledge_core beliefs p n

def list_as_set {α : Type} (xs : list α) : set α := λ x, x ∈ xs

def get_beliefs (n : nat) : set (set Prop) := list_as_set (list.map (λ p, beliefs p n) people)

axiom initial_beliefs : common_knowledge (get_beliefs 0) (∃ p, color p)

def bool_ite {α : Type} (t f : α) : bool -> α
| ff := f
| tt := t

def see (p : person) : Prop := bool_ite (color p = tt) (color p = ff) (color p)

example : forall p, see p :=
begin
intro,
unfold see,
cases (color p),

unfold bool_ite,
unfold bool_ite,
end

def typeof {α : Sort _} (a : α) := α

axiom initial_beliefs' : forall (p q : person), p ≠ q -> see q ∈ beliefs p 0
axiom initial_beliefs'' : common_knowledge (get_beliefs 0) (typeof initial_beliefs')

namespace test

constants a a' : bool
constant beliefs : set Prop

axiom beliefs_rational : is_rational beliefs
axiom true_beliefs : true ∈ beliefs

example : (a = tt) -> ((a = tt) ∈ beliefs) :=
begin
intro,
apply beliefs_rational,

intro,
assumption,

apply true_beliefs,
end



end test