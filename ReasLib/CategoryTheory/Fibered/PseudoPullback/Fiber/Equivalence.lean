module

public import ReasLib.CategoryTheory.Functor.Equivalence
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber.Comparison.Forward.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber.Comparison.Inverse.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibre equivalences for based pseudo-pullbacks

This leaf packages the canonical fibre comparison and its explicit inverse as reusable
quasi-inverse data and as the equivalence between an actual pseudo-pullback fibre and its
categorical-pullback model.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback

universe u v uX uY uS vX vY vS

namespace CategoryTheory
namespace BasedCategory

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}
variable (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)

noncomputable section

namespace PseudoPullback
namespace Fiber

/-- The objectwise unit of the fibre comparison equivalence. -/
def comparison.unitIso.app :
    ∀ {U : C} (P : Functor.Fiber (PseudoPullback F G).p U),
      P ≅ (Fiber.comparison F G U ⋙ comparisonInverse F G U).obj P
  | _, ⟨_, rfl⟩ => Iso.refl _

/-- The objectwise unit is natural in morphisms of the actual pseudo-pullback fibre. -/
theorem comparison.unitIso.app.naturality
    {U : C} {P Q : Functor.Fiber (PseudoPullback F G).p U} (φ : P ⟶ Q) :
    φ ≫ (comparison.unitIso.app F G Q).hom =
      (comparison.unitIso.app F G P).hom ≫
        (Fiber.comparison F G U ⋙ comparisonInverse F G U).map φ := sorry

/-- The unit from the identity on the actual fibre to comparison followed by its explicit
inverse. -/
@[stacks 02XI "unit isomorphism of the fibre comparison"]
def comparison.unitIso (U : C) :
    𝟭 (Functor.Fiber (PseudoPullback F G).p U) ≅
      Fiber.comparison F G U ⋙ comparisonInverse F G U :=
  NatIso.ofComponents
    (comparison.unitIso.app F G)
    (fun φ ↦ comparison.unitIso.app.naturality F G φ)

/-- Forgetting a forward unit component gives the total identity morphism, up to its
reconstructed endpoint. -/
theorem comparison.unitIso.app.hom.fiberInclusion
    {U : C} (P : Functor.Fiber (PseudoPullback F G).p U) :
    HEq (Functor.Fiber.fiberInclusion.map (comparison.unitIso.app F G P).hom)
      (𝟙 P.1) := sorry

/-- Forgetting an inverse unit component gives the total identity morphism, up to its
reconstructed endpoint. -/
theorem comparison.unitIso.app.inv.fiberInclusion
    {U : C} (P : Functor.Fiber (PseudoPullback F G).p U) :
    HEq (Functor.Fiber.fiberInclusion.map (comparison.unitIso.app F G P).inv)
      (𝟙 P.1) := sorry

/-- The forward component of the packaged unit is its explicit objectwise component. -/
@[simp]
theorem comparison.unitIso.hom.app
    {U : C} (P : Functor.Fiber (PseudoPullback F G).p U) :
    (comparison.unitIso F G U).hom.app P = (comparison.unitIso.app F G P).hom := sorry

/-- The inverse component of the packaged unit is its explicit objectwise component. -/
@[simp]
theorem comparison.unitIso.inv.app
    {U : C} (P : Functor.Fiber (PseudoPullback F G).p U) :
    (comparison.unitIso F G U).inv.app P = (comparison.unitIso.app F G P).inv := sorry

/-- The objectwise counit of the fibre comparison equivalence. -/
def comparison.counitIso.app
    {U : C} (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (comparisonInverse F G U ⋙ Fiber.comparison F G U).obj P ≅ P :=
  Iso.refl _

/-- The objectwise counit is natural in morphisms of the categorical-pullback model. -/
theorem comparison.counitIso.app.naturality
    {U : C} {P Q : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)} (φ : P ⟶ Q) :
    (comparisonInverse F G U ⋙ Fiber.comparison F G U).map φ ≫
        (comparison.counitIso.app F G Q).hom =
      (comparison.counitIso.app F G P).hom ≫ φ := sorry

/-- The counit from the explicit inverse followed by the fibre comparison to the identity on
the categorical-pullback model. -/
@[stacks 02XI "counit isomorphism of the fibre comparison"]
def comparison.counitIso (U : C) :
    comparisonInverse F G U ⋙ Fiber.comparison F G U ≅
      𝟭 ((F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :=
  NatIso.ofComponents
    (comparison.counitIso.app F G)
    (fun φ ↦ comparison.counitIso.app.naturality F G φ)

/-- The forward objectwise counit component is the identity morphism. -/
@[simp]
theorem comparison.counitIso.app.hom
    {U : C} (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (comparison.counitIso.app F G P).hom = 𝟙 P := sorry

/-- The inverse objectwise counit component is the identity morphism. -/
@[simp]
theorem comparison.counitIso.app.inv
    {U : C} (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (comparison.counitIso.app F G P).inv = 𝟙 P := sorry

/-- The forward component of the packaged counit is its explicit objectwise component. -/
@[simp]
theorem comparison.counitIso.hom.app
    {U : C} (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (comparison.counitIso F G U).hom.app P =
      (comparison.counitIso.app F G P).hom := sorry

/-- The inverse component of the packaged counit is its explicit objectwise component. -/
@[simp]
theorem comparison.counitIso.inv.app
    {U : C} (P : (F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :
    (comparison.counitIso F G U).inv.app P =
      (comparison.counitIso.app F G P).inv := sorry

/-- Explicit quasi-inverse data for the canonical comparison from the actual pseudo-pullback
fibre to its categorical-pullback model. -/
@[stacks 02XI "explicit quasi-inverse for the fibre comparison"]
noncomputable def comparison.quasiInverse (U : C) :
    Functor.QuasiInverse (Fiber.comparison F G U) where
  inverse := comparisonInverse F G U
  unitIso := comparison.unitIso F G U
  counitIso := comparison.counitIso F G U

/-- The canonical fibre comparison is an equivalence. -/
instance comparison.isEquivalence {U : C} :
    (Fiber.comparison F G U).IsEquivalence := sorry
/- Proof strategy: apply `Functor.QuasiInverse.isEquivalence` to
`comparison.quasiInverse F G U`. -/

/-- The explicit inverse fibre comparison is an equivalence. -/
instance comparisonInverse.isEquivalence {U : C} :
    (comparisonInverse F G U).IsEquivalence := sorry
/- Proof strategy: apply `Functor.QuasiInverse.isEquivalence` to
`(comparison.quasiInverse F G U).symm`. -/

/-- The fibre over `U` of the explicit pseudo-pullback is
canonically equivalent to the pullback of the two fibre categories. -/
@[stacks 02XI "fiber of a based pseudo-pullback"]
noncomputable def comparison.equivalence (U : C) :
    Functor.Fiber (PseudoPullback F G).p U ≌
      ((F.fiberFunctor U) ⊡ (G.fiberFunctor U)) :=
  (comparison.quasiInverse F G U).adjointifyUnit

/- Data audit: `comparison.quasiInverse` and `comparison.equivalence` retain the explicit comparison,
inverse comparison, and objectwise identity isomorphisms above. Any `sorryAx` dependency lies
in functor laws, naturality, or equivalence coherence rather than selecting non-`Prop` data. -/

end Fiber

end PseudoPullback
end

end BasedCategory
end CategoryTheory
