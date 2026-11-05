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

set_option backward.isDefEq.respectTransparency false in
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
  let coeff {V W : Cᵒᵖ} (f : V ⟶ W) :
      Shrink.{w} (R.obj V) →+ Shrink.{w} (R.obj W) :=
    { toFun := fun a ↦ equivShrink.{w} (R.obj W)
        ((R.map f).hom ((equivShrink.{w} (R.obj V)).symm a))
      map_zero' := by
        change equivShrink _ ((R.map f).hom ((equivShrink _).symm (equivShrink _ 0))) = equivShrink _ 0
        simp
      map_add' := by
        intro a b
        simp only [equivShrink_symm_add, map_add, equivShrink_add] }
  exact
    { obj V := ModuleCat.of (R.obj V)
        (((shrinkYoneda.{w}.obj X).obj V) →₀ Shrink.{w} (R.obj V))
      map {V W} f := ModuleCat.ofHom
        (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
          (ModuleCat.of (R.obj W)
            (((shrinkYoneda.{w}.obj X).obj W) →₀ Shrink.{w} (R.obj W))))
        { toFun := fun m ↦ Finsupp.mapDomain ((shrinkYoneda.{w}.obj X).map f)
            (m.mapRange (coeff f) (coeff f).map_zero)
          map_add' := by
            intro a b
            rw [Finsupp.mapRange_add (coeff f).map_add a b, Finsupp.mapDomain_add]
          map_smul' := by
            intro c m
            change Finsupp.mapDomain ((shrinkYoneda.{w}.obj X).map f)
              ((c • m).mapRange (coeff f) (coeff f).map_zero) =
              (R.map f).hom c • Finsupp.mapDomain ((shrinkYoneda.{w}.obj X).map f)
                (m.mapRange (coeff f) (coeff f).map_zero)
            rw [Finsupp.mapRange_smul' c ((R.map f).hom c) m (fun a ↦ ?_),
              Finsupp.mapDomain_smul]
            dsimp [coeff]
            simp only [equivShrink_symm_smul, smul_eq_mul, map_mul]
            exact equivShrink_smul ((R.map f).hom c)
              ((R.map f).hom ((equivShrink.{w} (R.obj V)).symm a)) }
      map_id := by
        intro V
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        change Finsupp.mapDomain ((shrinkYoneda.{w}.obj X).map (𝟙 V))
          (m.mapRange (coeff (𝟙 V)) (coeff (𝟙 V)).map_zero) = m
        have hc : coeff (𝟙 V) = AddMonoidHom.id _ := by
          ext a
          simp [coeff]
        rw [hc]
        rw [(shrinkYoneda.{w}.obj X).map_id V, ConcreteCategory.coe_id]
        change Finsupp.mapDomain id (Finsupp.mapRange id rfl m) = m
        rw [Finsupp.mapRange_id, Finsupp.mapDomain_id]
      map_comp := by
        intro V W Z f g
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        change Finsupp.mapDomain ((shrinkYoneda.{w}.obj X).map (f ≫ g))
          (m.mapRange (coeff (f ≫ g)) (coeff (f ≫ g)).map_zero) =
          Finsupp.mapDomain ((shrinkYoneda.{w}.obj X).map g)
            ((Finsupp.mapDomain ((shrinkYoneda.{w}.obj X).map f)
              (m.mapRange (coeff f) (coeff f).map_zero)).mapRange (coeff g) (coeff g).map_zero)
        have hc : coeff (f ≫ g) = (coeff g).comp (coeff f) := by
          ext a
          simp [coeff, Functor.map_comp]
        rw [hc, ← Finsupp.mapDomain_mapRange _ _ _ _ (coeff g).map_add]
        rw [← Finsupp.mapDomain_comp]
        simp only [Functor.map_comp, ConcreteCategory.coe_comp, AddMonoidHom.coe_comp,
          Finsupp.mapRange_mapRange] }



set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
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
                  (M.map (shrinkYonedaObjObjEquiv.{w} (X := X) (Y := V) a).op m : M.obj V)
              map_add' := by
                intro s t
                exact Finsupp.sum_add_index' (by intro a; simp <;> rfl) (by intros; simp [add_smul] <;> rfl)
              map_smul' := by
                intro c s
                change (c • s).sum _ = c • s.sum _
                rw [Finsupp.sum_smul_index', Finsupp.smul_sum]
                · apply Finsupp.sum_congr
                  intro a b
                  simp only [equivShrink_symm_smul, smul_assoc]
                · intro a
                  simp <;> rfl }
          naturality := by
            intro V W f
            apply ModuleCat.hom_ext
            apply Finsupp.lhom_ext
            intro a c
            dsimp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
              ModuleCat.RestrictScalars.map']
            simp [freeRepresentableOfUnivLE, Finsupp.sum_single_index,
              Finsupp.mapDomain_single]
            congr 1
            erw [shrinkYonedaObjObjEquiv_obj_map]
            simp only [op_comp, Quiver.Hom.op_unop, PresheafOfModules.map_comp_apply] }
      left_inv := by
        intro φ
        apply hom_ext
        intro V
        apply ModuleCat.hom_ext
        apply Finsupp.lhom_ext
        intro a c
        dsimp only [ModuleCat.hom_ofHom]
        simp only [LinearMap.coe_mk, AddHom.coe_mk,
          Finsupp.sum_single_index, equivShrink_symm_zero, zero_smul]
        have hn := naturality_apply φ
          (shrinkYonedaObjObjEquiv.{w} (X := X) (Y := V) a).op
          (Finsupp.single (shrinkYonedaObjObjEquiv.{w}.symm (𝟙 X))
            (equivShrink.{w} (R.obj (op X)) 1))
        simp [freeRepresentableOfUnivLE, Finsupp.mapDomain_single] at hn
        erw [shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm] at hn
        simp only [Quiver.Hom.unop_op, Category.comp_id, Equiv.symm_apply_apply] at hn
        erw [← hn, ← map_smul]
        congr 1
        rw [Finsupp.smul_single]
        congr 1
        apply (equivShrink.{w} (R.obj V)).symm.injective
        simp only [equivShrink_symm_smul, Equiv.symm_apply_apply, smul_eq_mul, mul_one]
      right_inv := by
        intro m
        dsimp only
        erw [ModuleCat.ofHom_apply]
        dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
        dsimp only [ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj', ModuleCat.of]
        simp only [Finsupp.sum_single_index, equivShrink_symm_zero, zero_smul,
          Equiv.symm_apply_apply, one_smul]
        erw [Equiv.apply_symm_apply]
        change M.map (𝟙 (op X)) m = m
        rw [M.map_id]
        rfl }



/-- The evaluation operation commutes with a specified module morphism. -/
theorem freeRepresentableOfUnivLEEquiv_comp
    {M N : PresheafOfModules.{w} R} {X : C}
    (f : freeRepresentableOfUnivLE R X ⟶ M) (g : M ⟶ N) :
    freeRepresentableOfUnivLEEquiv R (f ≫ g) =
      g.app _ (freeRepresentableOfUnivLEEquiv R f) := rfl

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
