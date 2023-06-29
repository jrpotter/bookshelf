import Bookshelf.Enderton.Set.OrderedPair

/-! # Relations

A representation of a relation, i.e. a set of ordered pairs. Like `Set`, it is
assumed a relation is homogeneous.
-/

namespace Set

/--
A relation type as defined by Enderton.

We choose to use tuples to represent our ordered pairs, as opposed to
Kuratowski's definition of a set.

Not to be confused with the Lean-provided `Rel`.
-/
abbrev Relation (α : Type _) := Set (α × α)

namespace Relation

/-! ## Domain and Range -/

/--
The domain of a `Relation`.
-/
def dom (R : Relation α) : Set α := Prod.fst '' R

/--
The first component of any pair in a `Relation` must be a member of the
`Relation`'s domain.
-/
theorem mem_pair_imp_fst_mem_dom {R : Relation α} (h : (x, y) ∈ R)
  : x ∈ dom R := by
  unfold dom Prod.fst
  simp only [mem_image, Prod.exists, exists_and_right, exists_eq_right]
  exact ⟨y, h⟩

/--
If `x ∈ dom R`, there exists some `y` such that `⟨x, y⟩ ∈ R`.
-/
theorem dom_exists {R : Relation α} (hx : x ∈ R.dom)
  : ∃ y : α, (x, y) ∈ R := by
  unfold dom at hx
  simp only [mem_image, Prod.exists, exists_and_right, exists_eq_right] at hx
  exact hx

/--
The range of a `Relation`.
-/
def ran (R : Relation α) : Set α := Prod.snd '' R

theorem mem_pair_imp_snd_mem_ran {R : Relation α} (h : (x, y) ∈ R)
  : y ∈ ran R := by
  unfold ran Prod.snd
  simp only [mem_image, Prod.exists, exists_eq_right]
  exact ⟨x, h⟩

/--
If `x ∈ ran R`, there exists some `t` such that `⟨t, x⟩ ∈ R`.
-/
theorem ran_exists {R : Relation α} (hx : x ∈ R.ran)
  : ∃ t : α, (t, x) ∈ R := by
  unfold ran at hx
  simp only [mem_image, Prod.exists, exists_eq_right] at hx
  exact hx

/--
The field of a `Relation`.
-/
def fld (R : Relation α) : Set α := dom R ∪ ran R

/--
The inverse of a `Relation`.
-/
def inv (R : Relation α) : Relation α := { (p.2, p.1) | p ∈ R }

/--
`(x, y)` is a member of relation `R` **iff** `(y, x)` is a member of `R⁻¹`.
-/
@[simp]
theorem mem_self_comm_mem_inv {R : Relation α}
  : (y, x) ∈ R.inv ↔ (x, y) ∈ R := by
  unfold inv
  simp only [Prod.exists, mem_setOf_eq, Prod.mk.injEq]
  apply Iff.intro
  · intro ⟨x', y', hxy⟩
    rw [← hxy.right.left, ← hxy.right.right]
    exact hxy.left
  · intro hxy
    exact ⟨x, y, hxy, rfl, rfl⟩

/--
The inverse of the inverse of a `Relation` is the `Relation`.
-/
@[simp]
theorem inv_inv_eq_self (R : Relation α)
  : R.inv.inv = R := by
  unfold inv
  simp only [Prod.exists, Set.mem_setOf_eq, Prod.mk.injEq]
  ext x
  apply Iff.intro
  · intro hx
    have ⟨a₁, b₁, ⟨⟨a₂, b₂, h₁⟩, h₂⟩⟩ := hx
    rw [← h₂, ← h₁.right.right, ← h₁.right.left]
    exact h₁.left
  · intro hx
    have (p, q) := x
    refine ⟨q, p, ⟨?_, ?_⟩⟩
    · exact ⟨p, q, hx, rfl, rfl⟩
    · rfl

/--
For a set `F`, `dom F⁻¹ = ran F`.
-/
@[simp]
theorem dom_inv_eq_ran_self {F : Relation α}
  : dom (F.inv) = ran F := by
  ext x
  unfold dom ran inv
  simp only [
    Prod.exists,
    Set.mem_image,
    Set.mem_setOf_eq,
    Prod.mk.injEq,
    exists_and_right,
    exists_eq_right
  ]
  apply Iff.intro
  · intro ⟨y, a, _, h⟩
    rw [← h.right.left]
    exact ⟨a, h.left⟩
  · intro ⟨y, hy⟩
    exact ⟨y, y, x, hy, rfl, rfl⟩

/--
For a set `F`, `ran F⁻¹ = dom F`.
-/
@[simp]
theorem ran_inv_eq_dom_self {F : Relation α}
  : ran (F.inv) = dom F := by
  ext x
  unfold dom ran inv
  simp only [
    Prod.exists,
    Set.mem_image,
    Set.mem_setOf_eq,
    Prod.mk.injEq,
    exists_eq_right,
    exists_and_right
  ]
  apply Iff.intro
  · intro ⟨a, y, b, h⟩
    rw [← h.right.right]
    exact ⟨b, h.left⟩
  · intro ⟨y, hy⟩
    exact ⟨y, x, y, hy, rfl, rfl⟩

/-! ## Restriction -/

/--
The restriction of a `Relation` to a `Set`.
-/
def restriction (R : Relation α) (A : Set α) : Relation α :=
  { p ∈ R | p.1 ∈ A } 

/-! ## Image -/

/--
The image of a `Relation` under a `Set`.
-/
def image (R : Relation α) (A : Set α) : Set α :=
  { y | ∃ u ∈ A, (u, y) ∈ R }

/-! ## Single-Rooted and Single-Valued -/

/--
A `Relation` `R` is said to be single-rooted **iff** for all `y ∈ ran R`, there
exists exactly one `x` such that `⟨x, y⟩ ∈ R`.
-/
def isSingleRooted (R : Relation α) : Prop :=
  ∀ y ∈ R.ran, ∃! x, x ∈ R.dom ∧ (x, y) ∈ R

/--
A single-rooted `Relation` should map the same output to the same input.
-/
theorem single_rooted_eq_unique {R : Relation α} {x₁ x₂ y : α}
  (hR : R.isSingleRooted)
  : (x₁, y) ∈ R → (x₂, y) ∈ R → x₁ = x₂ := by
  intro hx₁ hx₂
  unfold isSingleRooted at hR
  have := hR y (mem_pair_imp_snd_mem_ran hx₁)
  have ⟨y₁, hy₁⟩ := this
  simp only [and_imp] at hy₁
  have h₁ := hy₁.right x₁ (mem_pair_imp_fst_mem_dom hx₁) hx₁
  have h₂ := hy₁.right x₂ (mem_pair_imp_fst_mem_dom hx₂) hx₂
  rw [h₁, h₂]

/--
A `Relation` `R` is said to be single-valued **iff** for all `x ∈ dom R`, there
exists exactly one `y` such that `⟨x, y⟩ ∈ R`.

Notice, a `Relation` that is single-valued is a function.
-/
def isSingleValued (R : Relation α) : Prop :=
  ∀ x ∈ R.dom, ∃! y, y ∈ R.ran ∧ (x, y) ∈ R

/--
A single-valued `Relation` should map the same input to the same output.
-/
theorem single_valued_eq_unique {R : Relation α} {x y₁ y₂ : α}
  (hR : R.isSingleValued)
  : (x, y₁) ∈ R → (x, y₂) ∈ R → y₁ = y₂ := by
  intro hy₁ hy₂
  unfold isSingleValued at hR
  have := hR x (mem_pair_imp_fst_mem_dom hy₁)
  have ⟨x₁, hx₁⟩ := this
  simp only [and_imp] at hx₁
  have h₁ := hx₁.right y₁ (mem_pair_imp_snd_mem_ran hy₁) hy₁
  have h₂ := hx₁.right y₂ (mem_pair_imp_snd_mem_ran hy₂) hy₂
  rw [h₁, h₂]

/--
For a set `F`, `F⁻¹` is a function **iff** `F` is single-rooted.
-/
theorem single_valued_inv_iff_single_rooted_self {F : Set.Relation α}
  : F.inv.isSingleValued ↔ F.isSingleRooted := by
  apply Iff.intro
  · intro hF
    unfold isSingleValued at hF
    simp only [
      dom_inv_eq_ran_self,
      ran_inv_eq_dom_self,
      mem_self_comm_mem_inv
    ] at hF
    suffices ∀ x ∈ F.ran, ∃! y, (y, x) ∈ F from hF
    intro x hx
    have ⟨y, hy⟩ := hF x hx
    simp only [
      ran_inv_eq_dom_self,
      mem_self_comm_mem_inv,
      and_imp
    ] at hy
    refine ⟨y, hy.left.right, ?_⟩
    intro y₁ hy₁
    exact hy.right y₁ (mem_pair_imp_fst_mem_dom hy₁) hy₁
  · intro hF
    unfold isSingleRooted at hF
    unfold isSingleValued
    simp only [
      dom_inv_eq_ran_self,
      ran_inv_eq_dom_self,
      mem_self_comm_mem_inv
    ]
    exact hF

/--
For a relation `F`, `F` is a function **iff** `F⁻¹` is single-rooted.
-/
theorem single_valued_self_iff_single_rooted_inv {F : Set.Relation α}
  : F.isSingleValued ↔ F.inv.isSingleRooted := by
  conv => lhs; rw [← inv_inv_eq_self F]
  rw [single_valued_inv_iff_single_rooted_self]

/--
A `Relation` `R` is one-to-one if it is a single-rooted function.
-/
def isOneToOne (R : Relation α) : Prop :=
  R.isSingleValued ∧ R.isSingleRooted

/--
A `Relation` is one-to-one **iff** it's inverse is.
-/
theorem one_to_one_self_iff_one_to_one_inv {R : Relation α}
  : R.isOneToOne ↔ R.inv.isOneToOne := by
  unfold isOneToOne isSingleValued isSingleRooted
  conv => rhs; simp only [
    dom_inv_eq_ran_self,
    ran_inv_eq_dom_self,
    mem_self_comm_mem_inv,
    eq_iff_iff
  ]
  apply Iff.intro <;>
  · intro ⟨hx, hy⟩
    exact ⟨hy, hx⟩


/-! ## Composition -/

/--
The composition of two `Relation`s.
-/
def comp (F G : Relation α) : Relation α :=
  { p | ∃ t : α, (p.1, t) ∈ G ∧ (t, p.2) ∈ F}

/--
If `x ∈ dom (F ∘ G)`, then `x ∈ dom G`.
-/
theorem dom_comp_imp_dom_self {F G : Relation α}
  : x ∈ dom (F.comp G) → x ∈ dom G := by
  unfold dom comp
  simp only [
    mem_image,
    mem_setOf_eq,
    Prod.exists,
    exists_and_right,
    exists_eq_right,
    forall_exists_index
  ]
  intro y t ht
  exact ⟨t, ht.left⟩

/--
If `y ∈ ran (F ∘ G)`, then `y ∈ ran F`.
-/
theorem ran_comp_imp_ran_self {F G : Relation α}
  : y ∈ ran (F.comp G) → y ∈ ran F := by
  unfold ran comp
  simp only [
    mem_image,
    mem_setOf_eq,
    Prod.exists,
    exists_eq_right,
    forall_exists_index
  ]
  intro x t ht
  exact ⟨t, ht.right⟩

/--
The composition of two functions is itself a function.
-/
theorem single_valued_comp_is_single_valued {F G : Relation α}
  (hF : F.isSingleValued) (hG : G.isSingleValued)
  : (F.comp G).isSingleValued := by
  unfold isSingleValued
  intro x hx
  have ⟨y, hxy⟩ := dom_exists hx
  have hy := mem_pair_imp_snd_mem_ran hxy
  refine ⟨y, ⟨hy, hxy⟩, ?_⟩
  simp only [and_imp]

  intro y₁ _ hxy₁
  unfold comp at hxy hxy₁
  simp only [mem_setOf_eq] at hxy hxy₁
  have ⟨t₁, ht₁⟩ := hxy
  have ⟨t₂, ht₂⟩ := hxy₁

  -- First show `t₁ = t₂` and then show `y = y₁`.
  have t_eq : t₁ = t₂ := by
    unfold isSingleValued at hG
    have ⟨t', ht'⟩ := hG x (mem_pair_imp_fst_mem_dom ht₁.left)
    simp only [and_imp] at ht'
    have ht₁' := ht'.right t₁ (mem_pair_imp_snd_mem_ran ht₁.left) ht₁.left
    have ht₂' := ht'.right t₂ (mem_pair_imp_snd_mem_ran ht₂.left) ht₂.left
    rw [ht₁', ht₂']

  unfold isSingleValued at hF
  rw [t_eq] at ht₁
  have ⟨y', hy'⟩ := hF t₂ (mem_pair_imp_fst_mem_dom ht₁.right)
  simp only [and_imp] at hy'
  have hk₁ := hy'.right y (mem_pair_imp_snd_mem_ran ht₁.right) ht₁.right
  have hk₂ := hy'.right y₁ (mem_pair_imp_snd_mem_ran ht₂.right) ht₂.right
  rw [hk₁, hk₂]

/--
For `Relation`s `F` and `G`, `(F ∘ G)⁻¹ = G⁻¹ ∘ F⁻¹`.
-/
theorem comp_inv_eq_inv_comp_inv {F G : Relation α}
  : (F.comp G).inv = G.inv.comp F.inv := by
  calc (F.comp G).inv
  _ = {p | ∃ t, (p.2, t) ∈ G ∧ (t, p.1) ∈ F} := by
    rw [Set.Subset.antisymm_iff]
    apply And.intro
    · unfold inv comp
      intro t ht
      simp only [mem_setOf_eq, Prod.exists] at ht
      have ⟨a, b, ⟨⟨p, hp⟩, hab⟩⟩ := ht
      rw [← hab]
      exact ⟨p, hp⟩
    · unfold inv comp
      intro (a, b) ⟨p, hp⟩
      simp only [mem_setOf_eq, Prod.exists, Prod.mk.injEq]
      exact ⟨b, a, ⟨p, hp⟩, rfl, rfl⟩
  _ = {p | ∃ t, (t, p.1) ∈ F ∧ (p.2, t) ∈ G} := by
    rw [Set.Subset.antisymm_iff]
    apply And.intro
    · intro (a, b) ht
      simp only [mem_setOf_eq] at *
      have ⟨t, p, q⟩ := ht
      exact ⟨t, q, p⟩
    · intro (a, b) ht
      simp only [mem_setOf_eq] at *
      have ⟨t, p, q⟩ := ht
      exact ⟨t, q, p⟩
  _ = {p | ∃ t, (p.1, t) ∈ F.inv ∧ (t, p.2) ∈ G.inv } := by
    rw [Set.Subset.antisymm_iff]
    apply And.intro
    · intro (a, b) ht
      simp only [mem_setOf_eq] at *
      have ⟨t, p, q⟩ := ht
      refine ⟨t, ?_, ?_⟩ <;> rwa [mem_self_comm_mem_inv]
    · intro (a, b) ht
      simp only [mem_setOf_eq] at *
      have ⟨t, p, q⟩ := ht
      refine ⟨t, ?_, ?_⟩ <;> rwa [← mem_self_comm_mem_inv]
  _ = comp (inv G) (inv F) := rfl

/--
Indicates `Relation` `F` is a function from `A` to `B`.

This is usually denoted as `F : A → B`.
-/
def mapsInto (F : Relation α) (A B : Set α) :=
  F.isSingleValued ∧ dom F = A ∧ ran F ⊆ B

/--
Indicates `Relation` `F` is a function from `A` to `ran F = B`.
-/
def mapsOnto (F : Relation α) (A B : Set α) :=
  F.isSingleValued ∧ dom F = A ∧ ran F = B

/-! ## Ordered Pairs -/

/--
Convert a `Relation` into an equivalent representation using `OrderedPair`s.
-/
def toOrderedPairs (R : Relation α) : Set (Set (Set α)) :=
  -- Notice here we are using `Set.image` and *not* `Set.Relation.image`.
  Set.image (fun (x, y) => OrderedPair x y) R

end Relation

end Set