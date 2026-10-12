/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Localization.Representable
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relocalization comparison for representable localization

This leaf records the mate comparison between localization at two objects of a
site.  It is separated from the base representable-localization equivalence
because it additionally uses composition and mate infrastructure.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v

noncomputable section

namespace CategoryTheory.GrothendieckTopology.RepresentableLocalization

variable {C : Type u} [Category.{v} C]

variable (J : GrothendieckTopology C)
variable {U V : C} (f : V ⟶ U)
variable [∀ G : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension G]
variable [∀ G : (Over V)ᵒᵖ ⥤ Type (max u v), (Over.forget V).op.HasLeftKanExtension G]
variable [HasWeakSheafify (J.over U) (Type (max u v))]
variable [HasWeakSheafify (J.over V) (Type (max u v))]
variable [HasWeakSheafify J (Type (max u v))]

/-- The mate-oriented relocalization comparison commutes with the maps to the target slice. -/
theorem relocalizationLowerShriekOverMapComponent_comm
    (G : Sheaf (J.over V) (Type (max u v))) :
    (Functor.sheafPullbackComp'
      (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f)).inv.app G ≫
        (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U) ⋙
          comparison J U).obj G).hom =
      ((comparison J V ⋙
        Over.map (J.sheafifiedRepresentableMap f)).obj G).hom := sorry

/-- The component of the mate-oriented relocalization lower-shriek comparison. -/
noncomputable def relocalizationLowerShriekOverMapComponent
    (G : Sheaf (J.over V) (Type (max u v))) :
    (comparison J V ⋙
        Over.map (J.sheafifiedRepresentableMap f)).obj G ⟶
      ((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U) ⋙
        comparison J U).obj G :=
  Over.homMk
    ((Functor.sheafPullbackComp'
      (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f)).inv.app G)
    (relocalizationLowerShriekOverMapComponent_comm J f G)

/-- The mate-oriented relocalization components are natural. -/
theorem relocalizationLowerShriekOverMapComponent_naturality
    {G G' : Sheaf (J.over V) (Type (max u v))} (η : G ⟶ G') :
    (comparison J V ⋙
        Over.map (J.sheafifiedRepresentableMap f)).map η ≫
        relocalizationLowerShriekOverMapComponent J f G' =
      relocalizationLowerShriekOverMapComponent J f G ≫
        ((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U) ⋙
          comparison J U).map η := sorry

/-- Postcomposition by `J.sheafifiedRepresentableMap f` is the relocalization lower shriek
under the representable-localization comparisons. -/
noncomputable def relocalizationLowerShriekOverMap :
    comparison J V ⋙
        Over.map (J.sheafifiedRepresentableMap f) ⟶
      (Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U) ⋙
        comparison J U :=
  NatTrans.mk
    (relocalizationLowerShriekOverMapComponent J f)
    (fun {_ _} η ↦ relocalizationLowerShriekOverMapComponent_naturality J f η)

/-- The relocalization lower-shriek comparison is invertible. -/
theorem relocalizationLowerShriekOverMap_isIso :
    IsIso (relocalizationLowerShriekOverMap J f) := sorry

/-- The inverse-image relocalization comparison is the right mate of the lower-shriek map. -/
@[stacks 04J5 "inverse-image comparison"]
noncomputable def relocalizationInverseImageOverPullback :
    J.overMapPullback (Type (max u v)) f ⋙
        comparison J V ⟶
      comparison J U ⋙
        Over.pullback (J.sheafifiedRepresentableMap f) :=
  (mateEquiv
      ((Over.map f).sheafAdjunctionContinuous
        (Type (max u v)) (J.over V) (J.over U))
      (Over.mapPullbackAdj (J.sheafifiedRepresentableMap f))
      (TwoSquare.mk
        (comparison J V)
        ((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U))
        (Over.map (J.sheafifiedRepresentableMap f))
        (comparison J U)
        (relocalizationLowerShriekOverMap J f))).natTrans

/-- The inverse-image relocalization comparison is invertible. -/
@[stacks 04J5 "invertibility"]
theorem relocalizationInverseImageOverPullback_isIso :
    IsIso (relocalizationInverseImageOverPullback J f) := sorry

end CategoryTheory.GrothendieckTopology.RepresentableLocalization
