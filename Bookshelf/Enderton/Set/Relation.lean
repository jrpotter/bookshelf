import Bookshelf.Enderton.Set.OrderedPair

/-! # Enderton.Set.Relation

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
abbrev HRelation (α β : Type ) := Set (α × β)

/--
A homogeneous variant of the `HRelation` type.
-/
abbrev Relation (α : Type _) := HRelation α α

namespace Relation

/-! ## Domain and Range -/

/--
The domain of a `Relation`.
-/
def dom (R : HRelation α β) : Set α := Prod.fst '' R

/--
The first component of any pair in a `Relation` must be a member of the
`Relation`'s domain.
-/
theorem mem_pair_imp_fst_mem_dom {R : HRelation α β} (h : (x, y) ∈ R)
  : x ∈ dom R := by
  unfold dom Prod.fst
  simp only [mem_image, Prod.exists, exists_and_right, exists_eq_right]
  exact ⟨y, h⟩

/--
If `x ∈ dom R`, there exists some `y` such that `⟨x, y⟩ ∈ R`.
-/
theorem dom_exists {R : HRelation α β} (hx : x ∈ dom R)
  : ∃ y : β, (x, y) ∈ R := by
  unfold dom at hx
  simp only [mem_image, Prod.exists, exists_and_right, exists_eq_right] at hx
  exact hx

/--
The range of a `Relation`.
-/
def ran (R : HRelation α β) : Set β := Prod.snd '' R

theorem mem_pair_imp_snd_mem_ran {R : HRelation α β} (h : (x, y) ∈ R)
  : y ∈ ran R := by
  unfold ran Prod.snd
  simp only [mem_image, Prod.exists, exists_eq_right]
  exact ⟨x, h⟩

/--
If `x ∈ ran R`, there exists some `t` such that `⟨t, x⟩ ∈ R`.
-/
theorem ran_exists {R : HRelation α β} (hx : x ∈ ran R)
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
def inv (R : HRelation α β) : HRelation β α := { (p.2, p.1) | p ∈ R }

/--
`(x, y)` is a member of relation `R` **iff** `(y, x)` is a member of `R⁻¹`.
-/
@[simp]
theorem mem_self_comm_mem_inv {R : HRelation α β}
  : (y, x) ∈ inv R ↔ (x, y) ∈ R := by
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
theorem inv_inv_eq_self (R : HRelation α β)
  : inv (inv R) = R := by
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
theorem dom_inv_eq_ran_self {F : HRelation α β}
  : dom (inv F) = ran F := by
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
theorem ran_inv_eq_dom_self {F : HRelation α β}
  : ran (inv F) = dom F := by
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
def restriction (R : HRelation α β) (A : Set α) : HRelation α β :=
  { p ∈ R | p.1 ∈ A } 

/-! ## Image -/

/--
The image of a `Relation` under a `Set`.
-/
def image (R : HRelation α β) (A : Set α) : Set β :=
  { y | ∃ u ∈ A, (u, y) ∈ R }

/-! ## Single-Rooted and Single-Valued -/

/--
A `Relation` `R` is said to be single-rooted **iff** for all `y ∈ ran R`, there
exists exactly one `x` such that `⟨x, y⟩ ∈ R`.
-/
def isSingleRooted (R : HRelation α β) : Prop :=
  ∀ y ∈ ran R, ∃! x, x ∈ dom R ∧ (x, y) ∈ R

/--
A single-rooted `Relation` should map the same output to the same input.
-/
theorem single_rooted_eq_unique {R : HRelation α β} {x₁ x₂ : α} {y : β}
  (hR : isSingleRooted R)
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
def isSingleValued (R : HRelation α β) : Prop :=
  ∀ x ∈ dom R, ∃! y, y ∈ ran R ∧ (x, y) ∈ R

/--
A single-valued `Relation` should map the same input to the same output.
-/
theorem single_valued_eq_unique {R : HRelation α β} {x : α} {y₁ y₂ : β}
  (hR : isSingleValued R)
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
theorem single_valued_inv_iff_single_rooted_self {F : HRelation α β}
  : isSingleValued (inv F) ↔ isSingleRooted F := by
  apply Iff.intro
  · intro hF
    unfold isSingleValued at hF
    simp only [
      dom_inv_eq_ran_self,
      ran_inv_eq_dom_self,
      mem_self_comm_mem_inv
    ] at hF
    suffices ∀ x ∈ ran F, ∃! y, (y, x) ∈ F from hF
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
theorem single_valued_self_iff_single_rooted_inv {F : HRelation α β}
  : isSingleValued F ↔ isSingleRooted (inv F) := by
  conv => lhs; rw [← inv_inv_eq_self F]
  rw [single_valued_inv_iff_single_rooted_self]

/--
The subset of a function must also be a function.
-/
theorem single_valued_subset {F G : HRelation α β}
  (hG : isSingleValued G) (h : F ⊆ G)
  : isSingleValued F := by
  unfold isSingleValued
  intro x hx
  have ⟨y, hy⟩ := dom_exists hx
  unfold ExistsUnique
  simp only
  refine ⟨y, ⟨mem_pair_imp_snd_mem_ran hy, hy⟩, ?_⟩
  intro y₁ hy₁
  exact single_valued_eq_unique hG (h hy₁.right) (h hy)

/-! ## Injections -/

/--
A `Relation` `R` is one-to-one if it is a single-rooted function.
-/
def isOneToOne (R : HRelation α β) : Prop :=
  isSingleValued R ∧ isSingleRooted R

/--
A `Relation` is one-to-one **iff** it's inverse is.
-/
theorem one_to_one_self_iff_one_to_one_inv {R : HRelation α β}
  : isOneToOne R ↔ isOneToOne (inv R) := by
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

/-! ## Surjections -/

/--
Indicates `Relation` `F` is a function from `A` to `B`.

This is usually denoted as `F : A → B`.
-/
structure mapsInto (F : HRelation α β) (A : Set α) (B : Set β) : Prop where
  is_func : isSingleValued F
  dom_eq : dom F = A
  ran_ss : ran F ⊆ B

/--
Indicates `Relation` `F` is a function from `A` to `ran F = B`.
-/
structure mapsOnto (F : HRelation α β) (A : Set α) (B : Set β) : Prop where
  is_func : isSingleValued F
  dom_eq : dom F = A
  ran_eq : ran F = B

/-! ## Composition -/

/--
The composition of two `Relation`s.
-/
def comp (F : HRelation β γ) (G : HRelation α β) : HRelation α γ :=
  { p | ∃ t : β, (p.1, t) ∈ G ∧ (t, p.2) ∈ F}

/--
If `x ∈ dom (F ∘ G)`, then `x ∈ dom G`.
-/
theorem dom_comp_imp_dom_self {F : HRelation β γ} {G : HRelation α β}
  : x ∈ dom (comp F G) → x ∈ dom G := by
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
theorem ran_comp_imp_ran_self {F : HRelation β γ} {G : HRelation α β}
  : y ∈ ran (comp F G) → y ∈ ran F := by
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
Composition of functions is associative.
-/
theorem comp_assoc {R : HRelation γ δ} {S : HRelation β γ} {T : HRelation α β}
  : comp (comp R S) T = comp R (comp S T) := by
  calc comp (comp R S) T
    _ = { p | ∃ t, (p.1, t) ∈ T ∧ (t, p.2) ∈ comp R S} := rfl
    _ = { p | ∃ t, (p.1, t) ∈ T ∧ (∃ a, (t, a) ∈ S ∧ (a, p.2) ∈ R) } := rfl
    _ = { p | ∃ t, ∃ a, ((p.1, t) ∈ T ∧ (t, a) ∈ S) ∧ (a, p.2) ∈ R } := by
      ext p
      simp only [mem_setOf_eq]
      apply Iff.intro
      · intro ⟨t, ht, a, ha⟩
        exact ⟨t, a, ⟨ht, ha.left⟩, ha.right⟩
      · intro ⟨t, a, h₁, h₂⟩
        exact ⟨t, h₁.left, a, h₁.right, h₂⟩
    _ = { p | ∃ a, ∃ t, ((p.1, t) ∈ T ∧ (t, a) ∈ S) ∧ (a, p.2) ∈ R } := by
      ext p
      simp only [mem_setOf_eq]
      apply Iff.intro
      · intro ⟨t, a, h⟩
        exact ⟨a, t, h⟩
      · intro ⟨a, t, h⟩
        exact ⟨t, a, h⟩
    _ = { p | ∃ a, (∃ t, (p.1, t) ∈ T ∧ (t, a) ∈ S) ∧ (a, p.2) ∈ R } := by
      ext p
      simp only [mem_setOf_eq]
      apply Iff.intro
      · intro ⟨a, t, h⟩
        exact ⟨a, ⟨t, h.left⟩, h.right⟩
      · intro ⟨a, ⟨t, ht⟩, ha⟩
        exact ⟨a, t, ht, ha⟩
    _ = { p | ∃ a, (p.1, a) ∈ comp S T ∧ (a, p.2) ∈ R } := rfl
    _ = comp R (comp S T) := rfl

/--
The composition of two functions is itself a function.
-/
theorem single_valued_comp_is_single_valued
  {F : HRelation β γ} {G : HRelation α β}
  (hF : isSingleValued F) (hG : isSingleValued G)
  : isSingleValued (comp F G) := by
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
theorem comp_inv_eq_inv_comp_inv {F : HRelation β γ} {G : HRelation α β}
  : inv (comp F G) = comp (inv G) (inv F) := by
  calc inv (comp F G)
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
  _ = {p | ∃ t, (p.1, t) ∈ inv F ∧ (t, p.2) ∈ inv G } := by
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

/-! ## Ordered Pairs -/

/--
Convert a `Relation` into an equivalent representation using `OrderedPair`s.
-/
def toOrderedPairs (R : Relation α) : Set (Set (Set α)) :=
  -- Notice here we are using `Set.image` and *not* `Set.Relation.image`.
  Set.image (fun (x, y) => OrderedPair x y) R

/-! ## Equivalence Classes -/

/--
A binary `Relation` `R` is **reflexive** on `A` **iff** `xRx` for all `x ∈ A`.
-/
def isReflexive (R : Relation α) (A : Set α) := ∀ x ∈ A, (x, x) ∈ R

/--
A binary `Relation` `R` is **symmetric** **iff** whenever `xRy` then `yRx`.
-/
def isSymmetric (R : Relation α) := ∀ {x y : α}, (x, y) ∈ R → (y, x) ∈ R

/--
A binary `Relation` `R` is **transitive** **iff** whenever `xRy` and `yRz`, then
`xRz`.
-/
def isTransitive (R : Relation α) :=
  ∀ {x y z : α}, (x, y) ∈ R → (y, z) ∈ R → (x, z) ∈ R

/--
`Relation` `R` is an **equivalence relation** on set `A` **iff** `R` is a binary
relation on `A` that is relexive on `A`, symmetric, and transitive.
-/
structure isEquivalence (R : Relation α) (A : Set α) : Prop where
  b_on : fld R ⊆ A
  refl : isReflexive R A
  symm : isSymmetric R
  trans : isTransitive R

/--
A set of members related to `x` via `Relation` `R`.

The term "neighborhood" here was chosen to reflect this relationship between `x`
and the members of the set. It isn't standard in anyway.
-/
def neighborhood (R : Relation α) (x : α) := { t | (x, t) ∈ R }

/--
Assume that `R` is an equivalence relation on `A` and that `x` and `y` belong
to `A`. Then `[x]_R = [y]_R ↔ xRy`.
-/
theorem neighborhood_iff_mem {R : Set.Relation α} {A : Set α} {x y : α}
  (hR : isEquivalence R A) (_ : x ∈ A) (hy : y ∈ A)
  : neighborhood R x = neighborhood R y ↔ (x, y) ∈ R := by
  apply Iff.intro
  · intro h
    have : y ∈ neighborhood R y :=  hR.refl y hy
    rwa [← h] at this
  · intro h
    rw [Set.ext_iff]
    intro t
    apply Iff.intro
    · intro ht
      have := hR.symm h
      exact hR.trans this ht
    · intro ht
      exact hR.trans h ht

/--
A **partition** `Π` of a set `A` is a set of nonempty subsets of `A` that is
disjoint and exhaustive.
-/
structure isPartition (P : Set (Set α)) (A : Set α) : Prop where
  p_subset : ∀ p ∈ P, p ⊆ A 
  nonempty : ∀ p ∈ P, Set.Nonempty p
  disjoint : ∀ a ∈ P, ∀ b, b ∈ P → a ≠ b → a ∩ b = ∅
  exhaustive : ∀ a ∈ A, ∃ p, p ∈ P ∧ a ∈ p

/--
The partition `A / R` induced by an equivalence relation `R`.
-/
def modEquiv {A : Set α} {R : Relation α} (_ : isEquivalence R A) :=
  {neighborhood R x | x ∈ A}

/--
Show the sets formed by `modEquiv` do indeed form a `partition`.
-/
theorem modEquiv_partition {A : Set α} {R : Relation α} (hR : isEquivalence R A)
  : isPartition (modEquiv hR) A := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    have ⟨x, hx⟩ := hp
    rw [← hx.right]
    show ∀ t, t ∈ neighborhood R x → t ∈ A
    intro t ht
    have : t ∈ fld R := Or.inr (mem_pair_imp_snd_mem_ran ht)
    exact hR.b_on this
  · intro p hp
    have ⟨x, hx⟩ := hp
    refine ⟨x, ?_⟩
    rw [← hx.right]
    exact hR.refl x hx.left
  · intro X hX Y hY nXY
    by_contra nh
    have nh' : Set.Nonempty (X ∩ Y) := by
      rw [← Set.nmem_singleton_empty]
      exact nh
    have ⟨x, hx⟩ := hX
    have ⟨y, hy⟩ := hY
    have ⟨z, hz⟩ := nh'
    rw [← hx.right, ← hy.right] at hz
    unfold neighborhood at hz
    simp only [mem_inter_iff, mem_setOf_eq] at hz
    have hz_mem : z ∈ A := by
      have : z ∈ fld R := Or.inr (mem_pair_imp_snd_mem_ran hz.left)
      exact hR.b_on this
    rw [
      ← neighborhood_iff_mem hR hx.left hz_mem,
      ← neighborhood_iff_mem hR hy.left hz_mem,
      hx.right, hy.right
    ] at hz
    rw [hz.left, hz.right] at nXY
    simp only [ne_eq, not_true] at nXY
  · intro x hx
    exact ⟨neighborhood R x, ⟨x, hx, rfl⟩, hR.refl x hx⟩

end Relation

end Set