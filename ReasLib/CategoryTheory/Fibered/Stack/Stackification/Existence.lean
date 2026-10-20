module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Criteria
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.Canonical
import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence and uniqueness of stackifications

The universe-polymorphic owner returns a cartesian based functor from an arbitrary fibred source
to a possibly universe-enlarged stack. Uniqueness is stated once for heterogeneous cartesian
comparisons, so fixed-universe and bundled clients can specialize the same API.
-/

@[expose] public section

universe u v uX vX
universe uS₀ vS₀ uS₁ vS₁ uS₂ vS₂

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
namespace Functor.IsFibered.Stackification

/-- Every fibred projection over a site admits a stackification in a sufficiently large
total-category universe, together with its heterogeneous cartesian comparison. -/
@[stacks 02ZN "universe-polymorphic existence of stackification"]
theorem existsOverSite
    (J : GrothendieckTopology C)
    {S : Type uX} [Category.{vX} S] (p : S ⥤ C) [p.IsFibered] :
    ∃ Y : StackOver.{
        u, v, max u (max v (max uX vX)), max u v vX} J,
      ∃ G : CartesianBasedFunctor p Y.p,
        CartesianBasedFunctor.IsStackification J G :=
  ⟨Functor.StackificationConstruction.canonicalTarget J p, Functor.StackificationConstruction.canonicalComparison J p,
    Functor.StackificationConstruction.canonicalIsStackification J p⟩

/-- An explicit stackification presentation of a fibred category.

`Presentation` is the Type-valued owner for the existence statement above.  It stores the target
stack, the comparison functor, and the stackification predicate; it does not attempt to choose a
particular construction of the target or duplicate the predicate's fields. -/
@[stacks 02ZN "explicit stackification presentation"]
structure Presentation
    (J : GrothendieckTopology C)
    {S : Type uX} [Category.{vX} S] (p : S ⥤ C) [p.IsFibered] where
  /-- The target stack in the chosen presentation. -/
  target : StackOver.{
      u, v, max u (max v (max uX vX)), max u v vX} J
  /-- The cartesian comparison from the original fibred category. -/
  comparison : CartesianBasedFunctor p target.p
  /-- The comparison satisfies the stackification conditions. -/
  isStackification : CartesianBasedFunctor.IsStackification J comparison

attribute [stacks 02ZN "stackification presentation target"] Presentation.target
attribute [stacks 02ZN "stackification presentation comparison"] Presentation.comparison
attribute [stacks 02ZN "stackification presentation predicate"] Presentation.isStackification

/-- Package explicitly supplied stackification presentation data. -/
@[stacks 02ZN "package explicit stackification presentation"]
def Presentation.of
    (J : GrothendieckTopology C)
    {S : Type uX} [Category.{vX} S] (p : S ⥤ C) [p.IsFibered]
    (Y : StackOver.{u, v, max u (max v (max uX vX)), max u v vX} J)
    (G : CartesianBasedFunctor p Y.p)
    (hG : CartesianBasedFunctor.IsStackification J G) :
    Presentation J p :=
  ⟨Y, G, hG⟩

/-- Convert the proposition-level stackification existence theorem into the named presentation
owner.  Callers with a concrete target and comparison should use `Presentation.of` instead. -/
@[stacks 02ZN "package an existential stackification presentation"]
noncomputable def Presentation.ofExists
    (J : GrothendieckTopology C)
    {S : Type uX} [Category.{vX} S] (p : S ⥤ C) [p.IsFibered]
    (h : ∃ Y : StackOver.{u, v, max u (max v (max uX vX)), max u v vX} J,
      ∃ G : CartesianBasedFunctor p Y.p,
        CartesianBasedFunctor.IsStackification J G) :
    Presentation J p where
  target := Classical.choose h
  comparison := Classical.choose (Classical.choose_spec h)
  isStackification := Classical.choose_spec (Classical.choose_spec h)

/-- Every fibred category has a nonempty type of stackification presentations. -/
@[stacks 02ZN "existence of stackification presentation data"]
theorem Presentation.nonempty
    (J : GrothendieckTopology C)
    {S : Type uX} [Category.{vX} S] (p : S ⥤ C) [p.IsFibered] :
    Nonempty (Presentation J p) :=
  ⟨Presentation.of J p (Functor.StackificationConstruction.canonicalTarget J p)
    (Functor.StackificationConstruction.canonicalComparison J p) (Functor.StackificationConstruction.canonicalIsStackification J p)⟩

/-- The concrete local-descent stackification presentation.

The target and comparison are the actual canonical construction. Downstream code can use
its fields and the `IsStackification` API directly. -/
@[stacks 02ZN "selected stackification presentation"]
noncomputable def presentation
    (J : GrothendieckTopology C)
    {S : Type uX} [Category.{vX} S] (p : S ⥤ C) [p.IsFibered] :
    Presentation J p :=
  Presentation.of J p (Functor.StackificationConstruction.canonicalTarget J p)
    (Functor.StackificationConstruction.canonicalComparison J p) (Functor.StackificationConstruction.canonicalIsStackification J p)

/- Data audit: `presentation` uses the actual canonical target and comparison.
`ofExists` remains an explicit conversion from a caller-supplied existence witness. -/

end Functor.IsFibered.Stackification

namespace CartesianBasedFunctor.IsStackification

variable {J : GrothendieckTopology C}

variable {S₀ : Type uS₀} {S₁ : Type uS₁} {S₂ : Type uS₂}
variable [Category.{vS₀} S₀] [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₀ : S₀ ⥤ C} {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}
variable [p₀.IsFibered] [p₁.IsFibered] [p₂.IsFibered]

/-- Explicit comparison data between two stackification presentations.

The comparison functor, its equivalence witness, and the structure isomorphism are the reusable
data.  The stackification proofs remain theorem arguments to the uniqueness API rather than being
duplicated as fields of this owner. -/
@[stacks 02ZN "explicit stackification comparison data"]
structure ComparisonChoice
    (G₁ : CartesianBasedFunctor p₀ p₁)
    (G₂ : CartesianBasedFunctor p₀ p₂) where
  /-- The equivalence between the two stackification targets. -/
  comparison : CartesianBasedFunctor p₁ p₂
  /-- The underlying based functor of the comparison is an equivalence. -/
  isEquivalence : comparison.toBasedFunctor.IsEquivalence
  /-- The comparison isomorphism over the common source. -/
  iso : (CartesianBasedFunctor.precomp p₂ G₁).obj comparison ≅ G₂

attribute [stacks 02ZN "stackification comparison functor"] ComparisonChoice.comparison
attribute [stacks 02ZN "stackification comparison equivalence"] ComparisonChoice.isEquivalence
attribute [stacks 02ZN "stackification comparison structure isomorphism"] ComparisonChoice.iso

/-- Package explicitly supplied stackification comparison data. -/
@[stacks 02ZN "package stackification comparison data"]
def ComparisonChoice.of
    {G₁ : CartesianBasedFunctor p₀ p₁}
    {G₂ : CartesianBasedFunctor p₀ p₂}
    (e : CartesianBasedFunctor p₁ p₂)
    (he : e.toBasedFunctor.IsEquivalence)
    (α : (CartesianBasedFunctor.precomp p₂ G₁).obj e ≅ G₂) :
    ComparisonChoice G₁ G₂ :=
  ⟨e, he, α⟩

/-- Forget the equivalence proof: a stackification comparison is a factorization of `G₂`
through `G₁`, i.e. lift data for the universal property `0435` of `G₁`. -/
@[stacks 0435 "stackification comparison as a lift through the first stackification"]
def ComparisonChoice.toLiftChoice
    {G₁ : CartesianBasedFunctor p₀ p₁}
    {G₂ : CartesianBasedFunctor p₀ p₂}
    (A : ComparisonChoice G₁ G₂) : LiftChoice (i := G₁) G₂ :=
  LiftChoice.of A.comparison A.iso

/-- Any factorization of one stackification through another is an equivalence over the base.
This is the equivalence half of the uniqueness clause of `02ZN`. -/
@[stacks 02ZN "a lift between two stackifications is an equivalence"]
theorem LiftChoice.isEquivalence
    {G₁ : CartesianBasedFunctor p₀ p₁}
    {G₂ : CartesianBasedFunctor p₀ p₂}
    (hG₁ : CartesianBasedFunctor.IsStackification J G₁)
    (hG₂ : CartesianBasedFunctor.IsStackification J G₂)
    (L : LiftChoice (i := G₁) G₂) :
    L.lift.toBasedFunctor.IsEquivalence := sorry

/-- A factorization of `G₂` through the stackification `G₁` is comparison data between the two
stackifications; the functor and structure isomorphism are exactly the supplied lift data. -/
@[stacks 02ZN "stackification comparison from a lift"]
def ComparisonChoice.ofLiftChoice
    {G₁ : CartesianBasedFunctor p₀ p₁}
    {G₂ : CartesianBasedFunctor p₀ p₂}
    (hG₁ : CartesianBasedFunctor.IsStackification J G₁)
    (hG₂ : CartesianBasedFunctor.IsStackification J G₂)
    (L : LiftChoice (i := G₁) G₂) : ComparisonChoice G₁ G₂ :=
  ⟨L.lift, LiftChoice.isEquivalence hG₁ hG₂ L, L.comparison⟩

/-- Convert the proposition-level comparison existence theorem into one named data owner.

This is the explicit proposition-to-data boundary.  Callers that already construct the target
equivalence should use `ComparisonChoice.of` instead of selecting a witness. -/
@[stacks 02ZN "package an existential stackification comparison"]
noncomputable def ComparisonChoice.ofExists
    {G₁ : CartesianBasedFunctor p₀ p₁}
    {G₂ : CartesianBasedFunctor p₀ p₂}
    (h : ∃ e : CartesianBasedFunctor p₁ p₂,
      e.toBasedFunctor.IsEquivalence ∧
        Nonempty ((CartesianBasedFunctor.precomp p₂ G₁).obj e ≅ G₂)) :
    ComparisonChoice G₁ G₂ where
  comparison := Classical.choose h
  isEquivalence := (Classical.choose_spec h).1
  iso := Classical.choice (Classical.choose_spec h).2

/-- The comparison between two stackification presentations: the universal-property lift of
`G₂` through `G₁` (`0435`), with its structure isomorphism. The functor and isomorphism are the
fields of the canonical heterogeneous lift owner `IsStackification.liftChoice`; no separate
comparison factory is used. -/
@[stacks 02ZN "selected stackification comparison"]
noncomputable def comparisonChoice
    {G₁ : CartesianBasedFunctor p₀ p₁}
    {G₂ : CartesianBasedFunctor p₀ p₂}
    (hG₁ : CartesianBasedFunctor.IsStackification J G₁)
    (hG₂ : CartesianBasedFunctor.IsStackification J G₂) :
    ComparisonChoice G₁ G₂ :=
  haveI := hG₂.isStack
  ComparisonChoice.ofLiftChoice hG₁ hG₂ (liftChoice hG₁ G₂)

/-- The selected comparison functor is the lift of `G₂` through `G₁`. -/
@[simp, stacks 0435 "selected stackification comparison is the universal lift"]
theorem comparisonChoice_toLiftChoice
    {G₁ : CartesianBasedFunctor p₀ p₁}
    {G₂ : CartesianBasedFunctor p₀ p₂}
    (hG₁ : CartesianBasedFunctor.IsStackification J G₁)
    (hG₂ : CartesianBasedFunctor.IsStackification J G₂) :
    haveI := hG₂.isStack
    (comparisonChoice hG₁ hG₂).toLiftChoice = liftChoice hG₁ G₂ := rfl

/-- Two heterogeneous stackification presentations admit an equivalence-over-base comparison
compatible with their structure maps. This is the existence projection of
`comparisonUnique`. -/
@[stacks 02ZN "existence projection of stackification uniqueness"]
theorem existsComparisonEquivalence
    (G₁ : CartesianBasedFunctor p₀ p₁)
    (G₂ : CartesianBasedFunctor p₀ p₂)
    (hG₁ : CartesianBasedFunctor.IsStackification J G₁)
    (hG₂ : CartesianBasedFunctor.IsStackification J G₂) :
    ∃ e : CartesianBasedFunctor p₁ p₂,
      e.toBasedFunctor.IsEquivalence ∧
        Nonempty ((CartesianBasedFunctor.precomp p₂ G₁).obj e ≅ G₂) :=
  ⟨(comparisonChoice hG₁ hG₂).comparison, (comparisonChoice hG₁ hG₂).isEquivalence,
    ⟨(comparisonChoice hG₁ hG₂).iso⟩⟩

/-- Two stackification presentations have a nonempty type of explicit comparison data. -/
@[stacks 02ZN "existence of explicit stackification comparison data"]
theorem ComparisonChoice.nonempty
    {G₁ : CartesianBasedFunctor p₀ p₁}
    {G₂ : CartesianBasedFunctor p₀ p₂}
    (hG₁ : CartesianBasedFunctor.IsStackification J G₁)
    (hG₂ : CartesianBasedFunctor.IsStackification J G₂) :
    Nonempty (ComparisonChoice G₁ G₂) :=
  ⟨comparisonChoice hG₁ hG₂⟩

/-- The compatible isomorphism between two explicit stackification comparisons. It is the
comparison of the two underlying lifts through `G₁` supplied by the canonical lift owner
`LiftChoice.comparisonIso`, i.e. the `04W9` Hom-category universal property. -/
@[stacks 02ZN "selected stackification comparison isomorphism"]
noncomputable def ComparisonChoice.comparisonIso
    {G₁ : CartesianBasedFunctor p₀ p₁}
    {G₂ : CartesianBasedFunctor p₀ p₂}
    (hG₁ : CartesianBasedFunctor.IsStackification J G₁)
    (hG₂ : CartesianBasedFunctor.IsStackification J G₂)
    (A B : ComparisonChoice G₁ G₂) : A.comparison ≅ B.comparison :=
  haveI := hG₂.isStack
  LiftChoice.comparisonIso hG₁ A.toLiftChoice B.toLiftChoice

/-- The stackification comparison isomorphism has the expected compatibility equation. -/
@[stacks 02ZN "specification of selected stackification comparison isomorphism"]
theorem ComparisonChoice.comparisonIso_spec
    {G₁ : CartesianBasedFunctor p₀ p₁}
    {G₂ : CartesianBasedFunctor p₀ p₂}
    (hG₁ : CartesianBasedFunctor.IsStackification J G₁)
    (hG₂ : CartesianBasedFunctor.IsStackification J G₂)
    (A B : ComparisonChoice G₁ G₂) :
    (CartesianBasedFunctor.precomp p₂ G₁).mapIso
        (ComparisonChoice.comparisonIso hG₁ hG₂ A B) ≪≫ B.iso = A.iso :=
  haveI := hG₂.isStack
  LiftChoice.comparisonIso_spec hG₁ A.toLiftChoice B.toLiftChoice

/-- Any compatible comparison isomorphism equals the selected one. -/
@[stacks 02ZN "uniqueness of selected stackification comparison isomorphism"]
theorem ComparisonChoice.comparisonIso_unique
    {G₁ : CartesianBasedFunctor p₀ p₁}
    {G₂ : CartesianBasedFunctor p₀ p₂}
    (hG₁ : CartesianBasedFunctor.IsStackification J G₁)
    (hG₂ : CartesianBasedFunctor.IsStackification J G₂)
    (A B : ComparisonChoice G₁ G₂)
    (β : A.comparison ≅ B.comparison)
    (hβ : (CartesianBasedFunctor.precomp p₂ G₁).mapIso β ≪≫ B.iso = A.iso) :
    β = ComparisonChoice.comparisonIso hG₁ hG₂ A B :=
  haveI := hG₂.isStack
  LiftChoice.comparisonIso_unique hG₁ A.toLiftChoice B.toLiftChoice β hβ

/-- Any two explicit stackification comparisons admit a unique compatible comparison isomorphism. -/
@[stacks 02ZN "existence and uniqueness of explicit stackification comparisons"]
theorem ComparisonChoice.existsUniqueIso
    {G₁ : CartesianBasedFunctor p₀ p₁}
    {G₂ : CartesianBasedFunctor p₀ p₂}
    (hG₁ : CartesianBasedFunctor.IsStackification J G₁)
    (hG₂ : CartesianBasedFunctor.IsStackification J G₂)
    (A B : ComparisonChoice G₁ G₂) :
    ∃! β : A.comparison ≅ B.comparison,
      (CartesianBasedFunctor.precomp p₂ G₁).mapIso β ≪≫ B.iso = A.iso :=
  ⟨ComparisonChoice.comparisonIso hG₁ hG₂ A B,
    ComparisonChoice.comparisonIso_spec hG₁ hG₂ A B,
    fun β hβ ↦ ComparisonChoice.comparisonIso_unique hG₁ hG₂ A B β hβ⟩

/-- Two heterogeneous stackification presentations have equivalent targets. A compatible
comparison functor exists and is unique up to a unique comparison isomorphism, without imposing a
common universe on the source or the two targets. -/
@[stacks 02ZN "heterogeneous uniqueness of stackification"]
theorem comparisonUnique
    (G₁ : CartesianBasedFunctor p₀ p₁)
    (G₂ : CartesianBasedFunctor p₀ p₂)
    (hG₁ : CartesianBasedFunctor.IsStackification J G₁)
    (hG₂ : CartesianBasedFunctor.IsStackification J G₂) :
    ∃ e : CartesianBasedFunctor p₁ p₂,
      e.toBasedFunctor.IsEquivalence ∧
        ∃ α : (CartesianBasedFunctor.precomp p₂ G₁).obj e ≅ G₂,
          ∀ (H : CartesianBasedFunctor p₁ p₂)
              (α' : (CartesianBasedFunctor.precomp p₂ G₁).obj H ≅ G₂),
            ∃! β : e ≅ H,
              (CartesianBasedFunctor.precomp p₂ G₁).mapIso β ≪≫ α' = α :=
  haveI := hG₂.isStack
  ⟨(comparisonChoice hG₁ hG₂).comparison, (comparisonChoice hG₁ hG₂).isEquivalence,
    (comparisonChoice hG₁ hG₂).iso, fun H α' ↦
      ComparisonChoice.existsUniqueIso hG₁ hG₂ (comparisonChoice hG₁ hG₂)
        (ComparisonChoice.ofLiftChoice hG₁ hG₂ (LiftChoice.of H α'))⟩

attribute [stacks 02ZP "uniqueness of stackification in groupoids"] comparisonUnique

/- Data audit: `Functor.IsFibered.Stackification.presentation` uses the actual
canonical target and comparison. `ComparisonChoice.of` and `ComparisonChoice.ofLiftChoice`
package supplied data, and `ComparisonChoice.ofExists` eliminates an explicitly supplied
existence witness. The unconditional `comparisonChoice` and `ComparisonChoice.comparisonIso`
no longer use separate comparison factories: their functor and isomorphism data are exactly the
fields of the canonical heterogeneous lift owner `IsStackification.liftChoice` and
`IsStackification.LiftChoice.comparisonIso` (`0435`/`04W9`). Those owners still select from
admitted lift existence/uniqueness statements; their actual construction is RL-0881, on which
RL-0843 depends. Only the equivalence proof `LiftChoice.isEquivalence` is Prop proof debt here. -/

end CartesianBasedFunctor.IsStackification

end CategoryTheory
