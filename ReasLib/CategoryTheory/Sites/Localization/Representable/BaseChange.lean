/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Localization.Representable
public import ReasLib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Sites.Topos.Localized
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change for representable localization

This leaf compares representable-localization equivalences with pullback along
a continuous functor of sites.  It is separate from the construction of the
equivalence itself and from relocalization within one site.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v

namespace CategoryTheory.GrothendieckTopology.RepresentableLocalization

section Parameter

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : Functor D C) [u.IsContinuous JD JC]
variable [HasWeakSheafify JD (Type (max u v))]
variable [HasWeakSheafify JC (Type (max u v))]
variable [∀ P : Functor Dᵒᵖ (Type (max u v)), u.op.HasLeftKanExtension P]

/-- The canonical map from the sheafified representable at `U` to the inverse image of the
sheafified representable at `V`, attached to `c : U ⟶ u.obj V`.  Naming this map keeps
representable specializations of localized morphisms independent of the implementation of the
localization comparison. -/
@[stacks 04J9 "localization parameter"]
noncomputable abbrev baseChangeMap {V : D} {U : C} (c : U ⟶ u.obj V) :
    JC.sheafifiedRepresentable U ⟶
      (u.sheafPullback (Type (max u v)) JD JC).obj
        (JD.sheafifiedRepresentable V) :=
  JC.sheafifiedRepresentableMap c ≫
    Functor.SheafifiedRepresentable.pullbackComparison u JD JC V

/-- The representable base-change parameters associated to a commuting square
`c' ≫ u.map b = a ≫ c` form the corresponding commuting square of sheaves. -/
@[stacks 04J9 "parameter naturality"]
theorem baseChangeMap_naturality {V V' : D} {U U' : C}
    (c : U ⟶ u.obj V) (b : V' ⟶ V) (a : U' ⟶ U)
    (c' : U' ⟶ u.obj V') (h : c' ≫ u.map b = a ≫ c) :
    baseChangeMap u c' ≫
        (u.sheafPullback (Type (max u v)) JD JC).map
          (JD.sheafifiedRepresentableMap b) =
      JC.sheafifiedRepresentableMap a ≫ baseChangeMap u c := sorry

end Parameter

section LocalizedInverseImage

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : D ⥤ C) [u.IsContinuous JD JC]
variable {V : D} {U : C} (c : U ⟶ u.obj V)
variable [HasWeakSheafify JD (Type (max u v))]
variable [HasWeakSheafify JC (Type (max u v))]
variable [∀ P : Dᵒᵖ ⥤ Type (max u v), u.op.HasLeftKanExtension P]
variable [HasWeakSheafify (JD.over V) (Type (max u v))]
variable [∀ P : (Over V)ᵒᵖ ⥤ Type (max u v),
  (Over.forget V).op.HasLeftKanExtension P]
variable [HasWeakSheafify (JC.over (u.obj V)) (Type (max u v))]
variable [∀ P : (Over V)ᵒᵖ ⥤ Type (max u v),
  (Over.post u).op.HasLeftKanExtension P]

variable [PreservesFiniteLimits
  ((Over.post u).sheafPullback (Type (max u v)) (JD.over V) (JC.over (u.obj V)))]
variable [HasSheafify (JC.over U) (Type (max u v))]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type (max u v),
  (Over.forget U).op.HasLeftKanExtension P]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type (max u v),
  (Over.map c).op.HasPointwiseRightKanExtension P]

/-- Under representable localization, the inverse image of the localized morphism induced by
`c : U ⟶ u.obj V` is pullback along the composite of the representable map and the canonical
pullback comparison. -/
theorem localizedInverseImage :
    IsIsomorphic
      ((u.localizedMorphismOfTopoi c).inverseImage ⋙
        comparison JC U)
      (comparison JD V ⋙
        Over.post (u.sheafPullback (Type (max u v)) JD JC) ⋙
        Over.pullback (baseChangeMap u c)) := sorry

end LocalizedInverseImage

section SheafPullbackAlong

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : D ⥤ C) [u.IsContinuous JD JC]
variable [HasWeakSheafify JD (Type (max u v))]
variable [HasWeakSheafify JC (Type (max u v))]
variable [∀ P : Dᵒᵖ ⥤ Type (max u v), u.op.HasLeftKanExtension P]

variable {V : D} {U : C} (c : U ⟶ u.obj V)
variable [∀ P : (Over V)ᵒᵖ ⥤ Type (max u v),
  (Over.forget V).op.HasLeftKanExtension P]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type (max u v),
  (Over.forget U).op.HasLeftKanExtension P]
variable [HasWeakSheafify (JD.over V) (Type (max u v))]
variable [HasWeakSheafify (JC.over U) (Type (max u v))]

/-- Sheaf pullback commutes with representable localization and pullback along the map induced
by `c : U ⟶ u.obj V`. -/
@[stacks 04J9 "underlying topos"]
theorem sheafPullbackOverPullback :
    IsIsomorphic
      (u.sheafPullback (Type (max u v)) JD JC ⋙
        JC.overPullback (Type (max u v)) U ⋙
        comparison JC U)
      (JD.overPullback (Type (max u v)) V ⋙
        comparison JD V ⋙
        Over.post (u.sheafPullback (Type (max u v)) JD JC) ⋙
        Over.pullback (baseChangeMap u c)) := sorry

end SheafPullbackAlong

section SheafPullbackAtImage

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : D ⥤ C) [u.IsContinuous JD JC]
variable [HasWeakSheafify JD (Type (max u v))]
variable [HasWeakSheafify JC (Type (max u v))]
variable [∀ P : Dᵒᵖ ⥤ Type (max u v), u.op.HasLeftKanExtension P]
variable (V : D)
variable [∀ P : (Over V)ᵒᵖ ⥤ Type (max u v),
  (Over.forget V).op.HasLeftKanExtension P]
variable [∀ P : (Over (u.obj V))ᵒᵖ ⥤ Type (max u v),
  (Over.forget (u.obj V)).op.HasLeftKanExtension P]
variable [HasWeakSheafify (JD.over V) (Type (max u v))]
variable [HasWeakSheafify (JC.over (u.obj V)) (Type (max u v))]

/-- The identity-object specialization of `sheafPullbackOverPullback`, stated with the canonical
representable pullback comparison rather than a redundant identity representable map. -/
theorem sheafPullbackAtImage :
    IsIsomorphic
      (u.sheafPullback (Type (max u v)) JD JC ⋙
        JC.overPullback (Type (max u v)) (u.obj V) ⋙
        comparison JC (u.obj V))
      (JD.overPullback (Type (max u v)) V ⋙
        comparison JD V ⋙
        Over.post (u.sheafPullback (Type (max u v)) JD JC) ⋙
        Over.pullback (Functor.SheafifiedRepresentable.pullbackComparison u JD JC V)) := sorry

end SheafPullbackAtImage

end CategoryTheory.GrothendieckTopology.RepresentableLocalization
