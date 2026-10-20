/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.GrothendieckLarge
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.CategoryTheory.ShrinkYoneda

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u v r w

namespace PresheafOfModules

section Free

variable {C : Type u} [Category.{v} C] [UnivLE.{max v r, w}]
  (R : Cᵒᵖ ⥤ RingCat.{r})

/-- The represented free module presheaf in the supplied module universe.
Only the arrows and coefficient carriers need the supplied universe bound;
the object universe of the site may be larger. -/
def freeRepresentableOfUnivLE (X : C) : PresheafOfModules.{w} R := by
  letI : LocallySmall.{w} C :=
    ⟨fun X Y ↦ @Small.trans_univLE.{max v r, w, v} (X ⟶ Y)
      (small_max.{r} (X ⟶ Y)) inferInstance⟩
  letI : ∀ V : Cᵒᵖ, Small.{w} (R.obj V) := fun V ↦
    @Small.trans_univLE.{max v r, w, r} (R.obj V)
      (small_max.{v} (R.obj V)) inferInstance
  exact
    { obj V := ModuleCat.of (R.obj V)
        (((shrinkYoneda.{w}.obj X).obj V) →₀ Shrink.{w} (R.obj V))
      map {V W} f := ModuleCat.ofHom
        (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
          (ModuleCat.of (R.obj W)
            (((shrinkYoneda.{w}.obj X).obj W) →₀ Shrink.{w} (R.obj W))))
        { toFun := fun m ↦ Finsupp.mapDomain ((shrinkYoneda.{w}.obj X).map f)
            (m.mapRange
              (fun a ↦ equivShrink.{w} (R.obj W)
                ((R.map f).hom ((equivShrink.{w} (R.obj V)).symm a)))
              (by sorry))
          map_add' := by sorry
          map_smul' := by sorry }
      map_id := by sorry
      map_comp := by sorry }


/-- Evaluate a represented free module map at the identity basis vector;
the reverse map sends each basis arrow to restriction of the chosen section. -/
def freeRepresentableOfUnivLEEquiv {M : PresheafOfModules.{w} R} {X : C} :
    (freeRepresentableOfUnivLE R X ⟶ M) ≃ M.obj (op X) := by
  letI : LocallySmall.{w} C :=
    ⟨fun X Y ↦ @Small.trans_univLE.{max v r, w, v} (X ⟶ Y)
      (small_max.{r} (X ⟶ Y)) inferInstance⟩
  letI : ∀ V : Cᵒᵖ, Small.{w} (R.obj V) := fun V ↦
    @Small.trans_univLE.{max v r, w, r} (R.obj V)
      (small_max.{v} (R.obj V)) inferInstance
  exact
    { toFun f := f.app (op X) (Finsupp.single
        (shrinkYonedaObjObjEquiv.{w}.symm (𝟙 X)) (equivShrink.{w} (R.obj (op X)) 1))
      invFun m :=
        { app V := ModuleCat.ofHom
            { toFun := fun s ↦ Finsupp.sum s fun a c ↦
                (equivShrink.{w} (R.obj V)).symm c •
                  M.map (shrinkYonedaObjObjEquiv.{w} (X := X) (Y := V) a).op m
              map_add' := by sorry
              map_smul' := by sorry }
          naturality := by sorry }
      left_inv := by sorry
      right_inv := by sorry }


/-- The evaluation operation commutes with a specified module morphism. -/
theorem freeRepresentableOfUnivLEEquiv_comp
    {M N : PresheafOfModules.{w} R} {X : C}
    (f : freeRepresentableOfUnivLE R X ⟶ M) (g : M ⟶ N) :
    freeRepresentableOfUnivLEEquiv R (f ≫ g) =
      g.app _ (freeRepresentableOfUnivLEEquiv R f) := sorry

end Free

section Generator

variable {C : Type u} [Category.{v} C] [UnivLE.{max u v r, w}]
  (R : Cᵒᵖ ⥤ RingCat.{r})

/-- The coproduct of the actual represented free modules, indexed in the
supplied module universe. -/
def generatorOfUnivLE : PresheafOfModules.{w} R := by
  letI : Small.{w} C :=
    @Small.trans_univLE.{max u v r, w, u} C (small_max.{max v r} C) inferInstance
  letI : UnivLE.{max v r, w} :=
    @UnivLE.trans.{max v r, max u v r, w} (univLE_max.{max v r, u}) inferInstance
  exact ∐ fun X : Shrink.{w} C ↦ freeRepresentableOfUnivLE R ((equivShrink.{w} C).symm X)

/-- Maps from the displayed free-module coproduct separate module morphisms. -/
theorem generatorOfUnivLE_isSeparator : IsSeparator (generatorOfUnivLE R) := sorry

end Generator

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [UnivLE.{max u v r, w}]
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (R : Sheaf J RingCat.{r})

/-- The specified free-module generator followed by actual module sheafification. -/
def generatorOfUnivLE : SheafOfModules.{w} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    (PresheafOfModules.generatorOfUnivLE R.obj)

/-- The sheafification adjunction preserves separation by the specified generator. -/
theorem generatorOfUnivLE_isSeparator : IsSeparator (generatorOfUnivLE R) := sorry

end SheafOfModules
