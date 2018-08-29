inductive person : Type
| dan, tina
open person

@[reducible] def timestep := ℕ

constant is_marked : person → Prop

constant knows (t : timestep) (n : person) (p : Prop) : Prop

@[reducible] def mk_prec (p : timestep → person → Prop) : ℕ → timestep → person → Prop
| 0     t  n  := p t n
| (d+1) t₁ n₁ := ∀ {t₂ : timestep} {n₂ : person}, knows t₁ n₁ (mk_prec d t₂ n₂)

@[reducible] def pcommon_knowledge (pr : timestep → person → Prop) : Prop :=
  ∀ (d : ℕ) {t : timestep} {n : person}, mk_prec pr d t n

axiom knows_persists {p : Prop}   : pcommon_knowledge (λ t n, knows t n p → knows (t+1) n p)
axiom knows_lam      {p q : Prop} : pcommon_knowledge (λ t n, (knows t n p → knows t n q) → knows t n (p → q))
axiom knows_mp       {p q : Prop} : pcommon_knowledge (λ t n, knows t n (p → q) → knows t n p → knows t n q)
axiom knows_and      {p q : Prop} : pcommon_knowledge (λ t n, knows t n p → knows t n q → knows t n (p ∧ q))
axiom knows_sound    {p : Prop}   : pcommon_knowledge (λ t n, knows t n p → p)
axiom knows_cancel   {p q : Prop} : pcommon_knowledge (λ t n, knows t n (¬ p) → knows t n (p ∨ q) → knows t n q)
axiom knows_id       {p : Prop}   : pcommon_knowledge (λ t n, knows t n (p → p))
axiom knows_em       {p q : Prop} : pcommon_knowledge (λ t n, knows t n (p → q) → knows t n (¬ p → q) → knows t n q)

axiom oracle : pcommon_knowledge (λ t n, knows t n (is_marked dan ∨ is_marked tina))

@[reducible] def mk_rec (p : timestep → person → Prop) (t₁ t₂ : timestep) : person → ℕ → Prop
| n  0     := p t₂ n
| n₁ (d+1) := ∀ {n₂ : person}, knows t₁ n₁ (mk_rec n₂ d)

@[reducible] def common_knowledge (pr : timestep → person → Prop) (t₁ t₂ : timestep) : Prop :=
  ∀ (d : ℕ) {n : person}, mk_rec pr t₁ t₂ n d

axiom nobody_leaves : ∀ (t₁ t₂ : timestep), t₁ < 2 → t₁ < t₂ → common_knowledge (λ t n, ¬ knows t₁ n (is_marked n)) t₂ t₁

theorem T1 : knows 0 dan ((¬ is_marked dan) → knows 1 tina (is_marked tina)) :=
suffices H_suffices : knows 0 dan (¬ is_marked dan) → knows 0 dan (knows 1 tina (is_marked tina)), from knows_lam 0 H_suffices,
assume H1 : knows 0 dan (¬ is_marked dan),
show knows 0 dan (knows 1 tina (is_marked tina)), from

have H3a : knows 0 dan (knows 1 tina (is_marked dan → is_marked tina)), from
  suffices H_suffices : knows 0 dan (knows 1 tina (is_marked dan) → knows 1 tina (is_marked tina)),
    from knows_mp 0 (knows_lam 1) H_suffices,
  suffices H_suffices : knows 0 dan (knows 1 tina (is_marked dan)) → knows 0 dan (knows 1 tina (is_marked tina)),
    from knows_lam 0 H_suffices,
  assume h1 : knows 0 dan (knows 1 tina (is_marked dan)),
  absurd (knows_sound 0 (knows_sound 0 h1)) (knows_sound 0 H1),

have H3b : knows 0 dan (knows 1 tina (¬ is_marked dan → is_marked tina)), from
  suffices H_suffices : knows 0 dan (knows 1 tina (¬ is_marked dan) → knows 1 tina (is_marked tina)),
    from knows_mp 0 (knows_lam 1) H_suffices,
  suffices H_suffices : knows 0 dan (knows 1 tina (¬ is_marked dan)) → knows 0 dan (knows 1 tina (is_marked tina)),
    from knows_lam 0 H_suffices,
  assume h1 : knows 0 dan (knows 1 tina (¬ is_marked dan)),
  have   h2 : knows 0 dan (knows 1 tina (is_marked dan ∨ is_marked tina)), from knows_mp 0 (knows_persists 1) (oracle 1),
  have   h3 : knows 0 dan (knows 1 tina (¬ is_marked dan))
              → knows 0 dan (knows 1 tina (is_marked dan ∨ is_marked tina) → knows 1 tina (is_marked tina)), from knows_mp 0 (knows_cancel 1),
  have   h4 : knows 0 dan (knows 1 tina (¬ is_marked dan))
              → knows 0 dan (knows 1 tina (is_marked dan ∨ is_marked tina))
              → knows 0 dan (knows 1 tina (is_marked tina)), from assume z1 z2, knows_mp 0 (h3 z1) z2,
  h4 h1 (knows_mp 0 (knows_persists 1) (oracle 1)),

have Hem : ∀ {p q : Prop}, knows 0 dan (knows 1 tina (p → q)) → knows 0 dan (knows 1 tina ((¬ p) → q)) → knows 0 dan (knows 1 tina q), from
  begin intros p q z1, apply knows_mp 0, revert z1, apply knows_mp 0, exact knows_em 1 end,

Hem H3a H3b

theorem T2 : knows 0 dan (¬ knows 1 tina (is_marked tina) → is_marked dan) :=
suffices H_suffices : knows 0 dan (¬ knows 1 tina (is_marked tina)) → knows 0 dan (is_marked dan), from knows_lam 0 H_suffices,
assume H1 : knows 0 dan (¬ knows 1 tina (is_marked tina)),
have   H2 : knows 0 dan ((¬ is_marked dan) → knows 1 tina (is_marked tina)), from T1,
have   H3a : knows 0 dan (is_marked dan → is_marked dan), from knows_id 0,
have   H3b : knows 0 dan (¬ is_marked dan → is_marked dan), from
  suffices H_suffices : knows 0 dan (¬ is_marked dan) → knows 0 dan (is_marked dan), from knows_lam 0 H_suffices,
  assume h1 : knows 0 dan (¬ is_marked dan),
  show        knows 0 dan (is_marked dan), from
  have   h2 : knows 0 dan (knows 1 tina (is_marked tina)), from knows_mp 0 H2 h1,
  absurd (knows_sound 0 h2) (knows_sound 0 H1),
knows_em 0 H3a H3b

theorem T3 : knows 2 dan (is_marked dan) :=
have H1 : knows 2 dan (¬ knows 1 tina (is_marked tina) → is_marked dan), from knows_persists 0 (knows_persists 0 T2),
have H2 : knows 2 dan (¬ knows 1 tina (is_marked tina)), from nobody_leaves 1 2 (nat.lt_succ_self _) (nat.lt_succ_self _) 1,
show      knows 2 dan (is_marked dan), from
knows_mp 0 H1 H2
