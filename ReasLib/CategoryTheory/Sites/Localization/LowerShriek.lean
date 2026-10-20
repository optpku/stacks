module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.CategoryTheory.Limits.FiniteConnected.Preserves

/-!
# Exactness properties of slice localization lower shriek

These statements concern the left adjoint induced by the forgetful functor
`Over.forget U : Over U ⥤ C`.  They do not depend on an identification of the
slice topos with objects over a representable sheaf, so they are owned by the
generic slice-localization layer.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.GrothendieckTopology.Localization.LowerShriek

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} (U : C)
variable [∀ G : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension G]
variable [HasWeakSheafify J (Type (max u v))]

/-- Localization lower shriek preserves all finite connected limits.

This is the class-valued owner for the exactness statement. Preservation of any particular
finite connected shape, including pullbacks and equalizers, is supplied by
`PreservesFiniteConnectedLimits.preservesLimitsOfShape`. -/
instance preservesFiniteConnectedLimits :
    PreservesFiniteConnectedLimits
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J) := sorry

/-- Localization lower shriek preserves pullbacks. -/
theorem preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J) := sorry

/-- Localization lower shriek preserves equalizers. -/
theorem preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J) := sorry

/-- Localization lower shriek preserves monomorphisms. -/
instance preservesMonomorphisms :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).PreservesMonomorphisms := sorry

/-- Localization lower shriek reflects monomorphisms. -/
instance reflectsMonomorphisms :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).ReflectsMonomorphisms := sorry

/-- Localization lower shriek reflects epimorphisms. -/
instance reflectsEpimorphisms :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).ReflectsEpimorphisms := sorry

end CategoryTheory.GrothendieckTopology.Localization.LowerShriek
