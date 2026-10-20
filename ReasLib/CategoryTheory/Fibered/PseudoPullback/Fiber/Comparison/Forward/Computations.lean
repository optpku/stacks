module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber.Comparison.Forward.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for the forward fibre comparison

This leaf exposes the object, morphism, and structural-isomorphism readouts of the canonical
comparison from an actual pseudo-pullback fibre to its categorical-pullback model.
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

/-- The fibre comparison preserves the first object component. -/
@[simp] theorem comparison.obj.fst
    {U : C} (P : Functor.Fiber (PseudoPullback F G).p U) :
    ((Fiber.comparison F G U).obj P).fst.1 =
      PseudoPullback.fstObj (Functor.Fiber.fiberInclusion.obj P) := sorry

/-- The fibre comparison preserves the second object component. -/
@[simp] theorem comparison.obj.snd
    {U : C} (P : Functor.Fiber (PseudoPullback F G).p U) :
    ((Fiber.comparison F G U).obj P).snd.1 =
      PseudoPullback.sndObj (Functor.Fiber.fiberInclusion.obj P) := sorry

/-- The fibre comparison transports the stored comparison morphism along its two endpoint
equalities. -/
@[simp] theorem comparison.obj.comparisonHom
    {U : C} (P : Functor.Fiber (PseudoPullback F G).p U) :
    ((Fiber.comparison F G U).obj P).iso.hom.1 =
      F.toFunctor.map (eqToHom (comparison.obj.fst F G P)) ≫
        PseudoPullback.comparison (Functor.Fiber.fiberInclusion.obj P) ≫
          G.toFunctor.map (eqToHom (comparison.obj.snd F G P).symm) := sorry

/-- The full comparison isomorphism in the pullback model is obtained from the ambient
pseudo-pullback comparison by transporting both endpoints. This is the isomorphism-level
counterpart of `comparison.obj.comparisonHom`. -/
@[simp, stacks 02XI "comparison isomorphism in the modeled fibre"]
theorem comparison.obj.comparisonIso
    {U : C} (P : Functor.Fiber (PseudoPullback F G).p U) :
    (Functor.Fiber.fiberInclusion : S.p.Fiber U ⥤ S.obj).mapIso
        (((Fiber.comparison F G U).obj P).iso) =
      F.toFunctor.mapIso (eqToIso (comparison.obj.fst F G P)) ≪≫
        PseudoPullback.comparisonIsoApp (Functor.Fiber.fiberInclusion.obj P) ≪≫
          G.toFunctor.mapIso (eqToIso (comparison.obj.snd F G P).symm) := sorry

/-- The fibre comparison transports the first morphism component along its endpoint equalities. -/
@[simp] theorem comparison.map.fst
    {U : C} {P Q : Functor.Fiber (PseudoPullback F G).p U} (φ : P ⟶ Q) :
    ((Fiber.comparison F G U).map φ).fst.1 =
      eqToHom (comparison.obj.fst F G P) ≫
        PseudoPullback.fstMap (Functor.Fiber.fiberInclusion.map φ) ≫
          eqToHom (comparison.obj.fst F G Q).symm := sorry

/-- The fibre comparison transports the second morphism component along its endpoint equalities. -/
@[simp] theorem comparison.map.snd
    {U : C} {P Q : Functor.Fiber (PseudoPullback F G).p U} (φ : P ⟶ Q) :
    ((Fiber.comparison F G U).map φ).snd.1 =
      eqToHom (comparison.obj.snd F G P) ≫
        PseudoPullback.sndMap (Functor.Fiber.fiberInclusion.map φ) ≫
          eqToHom (comparison.obj.snd F G Q).symm := sorry

/-- The transported comparison morphism is heterogeneously equal to the original ambient
comparison morphism. -/
theorem comparison.obj.comparisonHom_heq
    {U : C} (P : Functor.Fiber (PseudoPullback F G).p U) :
    HEq (((Fiber.comparison F G U).obj P).iso.hom.1)
      (PseudoPullback.comparison (Functor.Fiber.fiberInclusion.obj P)) := sorry

/-- The transported first map component is heterogeneously equal to the original ambient map. -/
theorem comparison.map.fst_heq
    {U : C} {P Q : Functor.Fiber (PseudoPullback F G).p U} (φ : P ⟶ Q) :
    HEq (((Fiber.comparison F G U).map φ).fst.1)
      (PseudoPullback.fstMap (Functor.Fiber.fiberInclusion.map φ)) := sorry

/-- The transported second map component is heterogeneously equal to the original ambient map. -/
theorem comparison.map.snd_heq
    {U : C} {P Q : Functor.Fiber (PseudoPullback F G).p U} (φ : P ⟶ Q) :
    HEq (((Fiber.comparison F G U).map φ).snd.1)
      (PseudoPullback.sndMap (Functor.Fiber.fiberInclusion.map φ)) := sorry

end Fiber
end PseudoPullback
end

end BasedCategory
end CategoryTheory
