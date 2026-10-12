/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Criteria
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
        u, v, max u (max v (max uX vX)), max v vX} J,
      ∃ G : CartesianBasedFunctor p Y.p,
        CartesianBasedFunctor.IsStackification J G := sorry

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
      u, v, max u (max v (max uX vX)), max v vX} J
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
    (Y : StackOver.{u, v, max u (max v (max uX vX)), max v vX} J)
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
    (h : ∃ Y : StackOver.{u, v, max u (max v (max uX vX)), max v vX} J,
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
    Nonempty (Presentation J p) := sorry

/-- A convenient selected stackification presentation.

This is noncanonical choice data.  Downstream code should use its fields and the
`IsStackification` API rather than unfold the underlying choice. -/
@[stacks 02ZN "selected stackification presentation"]
noncomputable def presentation
    (J : GrothendieckTopology C)
    {S : Type uX} [Category.{vX} S] (p : S ⥤ C) [p.IsFibered] :
    Presentation J p :=
  Presentation.ofExists J p (existsOverSite J p)

/- Data audit: `Presentation` and `Presentation.of` carry only explicitly supplied target and
comparison data.  `ofExists` and `presentation` are the named proposition-to-data boundaries;
their `sorryAx` dependence, when present, is confined to the Prop-valued stackification field. -/

end Functor.IsFibered.Stackification

namespace CartesianBasedFunctor.IsStackification

variable {J : GrothendieckTopology C}

variable {S₀ : Type uS₀} {S₁ : Type uS₁} {S₂ : Type uS₂}
variable [Category.{vS₀} S₀] [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₀ : S₀ ⥤ C} {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}
variable [p₀.IsFibered] [p₁.IsFibered] [p₂.IsFibered]

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
              (CartesianBasedFunctor.precomp p₂ G₁).mapIso β ≪≫ α' = α := sorry

attribute [stacks 02ZP "uniqueness of stackification in groupoids"] comparisonUnique

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
        Nonempty ((CartesianBasedFunctor.precomp p₂ G₁).obj e ≅ G₂) := sorry

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

/-- Two stackification presentations have a nonempty type of explicit comparison data. -/
@[stacks 02ZN "existence of explicit stackification comparison data"]
theorem ComparisonChoice.nonempty
    {G₁ : CartesianBasedFunctor p₀ p₁}
    {G₂ : CartesianBasedFunctor p₀ p₂}
    (hG₁ : CartesianBasedFunctor.IsStackification J G₁)
    (hG₂ : CartesianBasedFunctor.IsStackification J G₂) :
    Nonempty (ComparisonChoice G₁ G₂) := sorry

/-- A convenient selected comparison between two stackification presentations.

This value is noncanonical; downstream code should use its fields and the uniqueness readout below
rather than unfolding the underlying choice. -/
@[stacks 02ZN "selected stackification comparison"]
noncomputable def comparisonChoice
    {G₁ : CartesianBasedFunctor p₀ p₁}
    {G₂ : CartesianBasedFunctor p₀ p₂}
    (hG₁ : CartesianBasedFunctor.IsStackification J G₁)
    (hG₂ : CartesianBasedFunctor.IsStackification J G₂) :
    ComparisonChoice G₁ G₂ :=
  ComparisonChoice.ofExists (existsComparisonEquivalence G₁ G₂ hG₁ hG₂)

/-- Any two explicit stackification comparisons admit a unique compatible comparison isomorphism. -/
@[stacks 02ZN "existence and uniqueness of explicit stackification comparisons"]
theorem ComparisonChoice.existsUniqueIso
    {G₁ : CartesianBasedFunctor p₀ p₁}
    {G₂ : CartesianBasedFunctor p₀ p₂}
    (hG₁ : CartesianBasedFunctor.IsStackification J G₁)
    (hG₂ : CartesianBasedFunctor.IsStackification J G₂)
    (A B : ComparisonChoice G₁ G₂) :
    ∃! β : A.comparison ≅ B.comparison,
      (CartesianBasedFunctor.precomp p₂ G₁).mapIso β ≪≫ B.iso = A.iso := sorry

/-- The selected compatible isomorphism between two explicit stackification comparisons. -/
@[stacks 02ZN "selected stackification comparison isomorphism"]
noncomputable def ComparisonChoice.comparisonIso
    {G₁ : CartesianBasedFunctor p₀ p₁}
    {G₂ : CartesianBasedFunctor p₀ p₂}
    (hG₁ : CartesianBasedFunctor.IsStackification J G₁)
    (hG₂ : CartesianBasedFunctor.IsStackification J G₂)
    (A B : ComparisonChoice G₁ G₂) : A.comparison ≅ B.comparison :=
  Classical.choose (ExistsUnique.exists
    (ComparisonChoice.existsUniqueIso hG₁ hG₂ A B))

/-- The selected stackification comparison isomorphism has the expected compatibility equation. -/
@[stacks 02ZN "specification of selected stackification comparison isomorphism"]
theorem ComparisonChoice.comparisonIso_spec
    {G₁ : CartesianBasedFunctor p₀ p₁}
    {G₂ : CartesianBasedFunctor p₀ p₂}
    (hG₁ : CartesianBasedFunctor.IsStackification J G₁)
    (hG₂ : CartesianBasedFunctor.IsStackification J G₂)
    (A B : ComparisonChoice G₁ G₂) :
    (CartesianBasedFunctor.precomp p₂ G₁).mapIso
        (ComparisonChoice.comparisonIso hG₁ hG₂ A B) ≪≫ B.iso = A.iso := sorry

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
    β = ComparisonChoice.comparisonIso hG₁ hG₂ A B := sorry

/- Data audit: `ComparisonChoice` and `ComparisonChoice.of` carry only supplied comparison data.
Any reported `sorryAx` is inherited from Prop-valued category, functor, and coherence laws in the
field types; no comparison functor or comparison isomorphism is synthesized by a placeholder.
`ofExists` is the explicit existential-elimination boundary, while `comparisonChoice` additionally
depends on the proposition-level stackification existence theorem. Downstream code should use the
field/spec/uniqueness API rather than unfold either selected value. -/

end CartesianBasedFunctor.IsStackification

end CategoryTheory
