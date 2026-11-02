/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.NaiveComparison
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.HomologyZero
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Cochain
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Ext comparisons for the sheaf cotangent complex

Good truncation identifies Ext¹ of the naive and full cotangent complexes, and the
augmentation identifies Ext⁰ with homomorphisms out of relative differentials.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits DerivedCategory HomologicalComplex
open SheafOfModules.RingedSite
open scoped DerivedExt SheafOfModules.RingedSite SheafOfModules.RingedSite.CotangentComplex

namespace SheafOfModules.RingedSite.CotangentComplex

private theorem cochain_to_single_eq_zero_of_homologyMap_eq_zero
    {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {K : CochainComplex 𝒜 ℤ} [K.IsStrictlyLE 0] {M : 𝒜}
    (g : K ⟶ (single 𝒜 (ComplexShape.up ℤ) 0).obj M)
    (hg : homologyMap g 0 = 0) : g = 0 := by
  apply to_single_hom_ext
  have hcy : cyclesMap g 0 = 0 := by
    apply (cancel_mono (singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 M).hom).1
    erw [← homologyπ_singleObjHomologySelfIso_hom,
      ← homologyπ_naturality_assoc, hg]
    simp only [comp_zero, zero_comp]
  haveI : IsIso (K.iCycles 0) :=
    K.isIso_iCycles 0 1 (by simp) (by
      exact (K.isZero_of_isStrictlyLE 0 1 (by decide)).eq_of_tgt _ _)
  change g.f 0 = 0
  apply (cancel_epi (K.iCycles 0)).1
  rw [← cyclesMap_i, hcy]
  simp only [zero_comp, comp_zero]

private theorem derived_to_single_eq_zero_of_homology_map_eq_zero
    {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]
    {K : CochainComplex 𝒜 ℤ} [K.IsStrictlyLE 0] {M : 𝒜}
    (e : DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj ((single 𝒜 (ComplexShape.up ℤ) 0).obj M))
    (he : (DerivedCategory.homologyFunctor 𝒜 0).map e = 0) : e = 0 := by
  obtain ⟨K', _, s, _, g, hfac⟩ := DerivedCategory.right_fac_of_isStrictlyLE e 0
  have hcomp : DerivedCategory.Q.map s ≫ e = DerivedCategory.Q.map g := by
    rw [hfac]
    simp
  have hg : (DerivedCategory.homologyFunctor 𝒜 0).map (DerivedCategory.Q.map g) = 0 := by
    rw [← hcomp, Functor.map_comp, he, comp_zero]
  have hnat := (DerivedCategory.homologyFunctorFactors 𝒜 0).hom.naturality g
  dsimp at hnat
  erw [hg, zero_comp] at hnat
  have hg' : homologyMap g 0 = 0 := by
    apply (cancel_epi ((DerivedCategory.homologyFunctorFactors 𝒜 0).hom.app K')).1
    erw [comp_zero]
    exact hnat.symm
  rw [hfac, cochain_to_single_eq_zero_of_homologyMap_eq_zero g hg',
    Functor.map_zero, comp_zero]

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]

-- Local instance justification (defeq pin): pin Q, singleFunctor, and Ext to the reducible standard derived category of the site-presented module category.
attribute [local instance] moduleCategoryHasDerivedCategory

variable {A B : Sheaf J CommRingCat.{u}}

variable (G : SheafOfModules.{u} (ringSheaf J B))

/-- The coefficient object `Q(G[0])` in `D(B)`. -/
abbrev coeffSingle : DerivedCategory (SheafOfModules (ringSheaf J B)) :=
  DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)

variable (φ : A ⟶ B) (G : SheafOfModules.{u} (ringSheaf J B))

/-- Derived morphism `L(φ) ⟶ (NaiveCotangent.obj A (Under.mk φ))` in `D(B)`. -/
def toNaiveDerived :
    DerivedCategory.Q.obj L(φ) ⟶
      DerivedCategory.Q.obj (NaiveCotangent.obj A (Under.mk φ)) :=
  DerivedCategory.Q.map (toNaive A (Under.mk φ))

/-- Section `(NaiveCotangent.obj A (Under.mk φ)) ⟶ τ_{≥ -1} L(φ)` in `D(B)`, via `πTruncGE`, the truncation
quasi-isomorphism of `toNaive`, and the canonical `qHom` comparison. -/
def toTruncGESection :
    DerivedCategory.Q.obj (NaiveCotangent.obj A (Under.mk φ)) ⟶
      (DerivedCategory.TStructure.t.truncGE (-1)).obj (DerivedCategory.Q.obj L(φ)) :=
  DerivedCategory.Q.map ((NaiveCotangent.obj A (Under.mk φ)).πTruncGE (-1)) ≫
    inv (DerivedCategory.Q.map (CochainComplex.truncGEMap (toNaive A (Under.mk φ)) (-1)))
      (I := (DerivedCategory.isIso_Q_map_iff_quasiIso
        (SheafOfModules (ringSheaf J B)) _).mpr
        (CotangentComplex.toNaive_truncGE_quasiIso A (Under.mk φ))) ≫
    inv (DerivedCategory.TruncGE.qHom L(φ) (-1))

/-- The shifted coefficient object `G[1]` lies in `t.GE (-1)`. -/
instance coeffSingle_shift_isGE :
    DerivedCategory.TStructure.t.IsGE ((coeffSingle G)⟦(1 : ℤ)⟧) (-1) :=
  DerivedCategory.TStructure.t.isGE_shift (coeffSingle G) (0 : ℤ) (1 : ℤ) (-1)

/-- The Ext¹ class of `(NaiveCotangent.obj A (Under.mk φ))` obtained from a derived Ext¹ class by `descTruncGE`
and `toTruncGESection`. -/
def fromDerivedToNaiveExt
    (η : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj L(φ), coeffSingle G)) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj A (Under.mk φ)), coeffSingle G) :=
  ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toTruncGESection φ))
    (DerivedCategory.TStructure.t.descTruncGE
      (η : DerivedCategory.Q.obj L(φ) ⟶ (coeffSingle G)⟦(1 : ℤ)⟧) (-1))
    (add_zero (1 : ℤ))

/-- The comparison and its truncation section recover the canonical truncation projection. -/
theorem toNaiveDerived_comp_toTruncGESection :
    toNaiveDerived φ ≫ toTruncGESection φ =
      (DerivedCategory.TStructure.t.truncGEπ (-1)).app (DerivedCategory.Q.obj L(φ)) := by
  unfold toNaiveDerived toTruncGESection
  rw [← Functor.map_comp_assoc, ← CochainComplex.πTruncGE_naturality,
    Functor.map_comp]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc,
    DerivedCategory.TruncGE.qHom.map_comp_inv]

/-- The naive-to-derived Ext¹ comparison of `(NaiveCotangent.obj A (Under.mk φ))` with `L(φ)`. -/
def extOneTruncEquiv :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj A (Under.mk φ)), coeffSingle G) ≃+
      Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj L(φ), coeffSingle G) where
  toFun ξ :=
    ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toNaiveDerived φ)) ξ (add_zero (1 : ℤ))
  invFun η := fromDerivedToNaiveExt φ G η
  left_inv ξ := by
    haveI : IsIso (toTruncGESection φ) := by
      unfold toTruncGESection
      infer_instance
    simp only [fromDerivedToNaiveExt, ShiftedHom.mk₀_comp]
    apply (cancel_epi (inv (toTruncGESection φ))).1
    apply DerivedCategory.TStructure.t.from_truncGE_obj_ext (n := -1)
    simp only [IsIso.inv_hom_id_assoc, DerivedCategory.TStructure.t.π_descTruncGE]
    rw [← toNaiveDerived_comp_toTruncGESection φ]
    erw [Category.assoc, IsIso.hom_inv_id_assoc]
    rfl
  right_inv η := by
    simp only [fromDerivedToNaiveExt, ShiftedHom.mk₀_comp, ← Category.assoc,
      toNaiveDerived_comp_toTruncGESection]
    exact DerivedCategory.TStructure.t.π_descTruncGE η (-1)
  map_add' ξ η := ShiftedHom.comp_add _ ξ η _

/-- The forward map of `extOneTruncEquiv` is precomposition along `toNaiveDerived`. -/
theorem extOneTruncEquiv_apply
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj A (Under.mk φ)), coeffSingle G)) :
    extOneTruncEquiv φ G ξ =
      ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toNaiveDerived φ)) ξ
        (add_zero (1 : ℤ)) :=
  rfl

/-- The unshifted morphism `L(φ) ⟶ G[0]` attached to a map out of `Ω(φ)`. -/
def homKaehlerDerived (α : Ω(φ) ⟶ G) :
    DerivedCategory.Q.obj L(φ) ⟶ coeffSingle G :=
  DerivedCategory.Q.map
    (CotangentComplex.augmentation φ ≫
      (CochainComplex.singleFunctor _ 0).map α)

/-- The Hom representative of an Ext⁰ class, obtained from `H^0` along `homologyZeroIso`. -/
def homOfExtZero (e : Ext⁽(0 : ℤ)⁾(DerivedCategory.Q.obj L(φ), coeffSingle G)) :
    Ω(φ) ⟶ G :=
  (homologyZeroIso φ).inv ≫
    (DerivedCategory.homologyFunctorFactors (SheafOfModules (ringSheaf J B)) (0 : ℤ)).inv.app
      L(φ) ≫
    (DerivedCategory.homologyFunctor (SheafOfModules (ringSheaf J B)) (0 : ℤ)).map
      ((ShiftedHom.homEquiv (0 : ℤ) rfl).symm e) ≫
    (DerivedCategory.homologyFunctorFactors (SheafOfModules (ringSheaf J B)) (0 : ℤ)).hom.app
      ((CochainComplex.singleFunctor _ 0).obj G) ≫
    (singleObjHomologySelfIso (ComplexShape.up ℤ) (0 : ℤ) G).hom

/-- Taking zeroth homology recovers the original map out of relative differentials. -/
theorem homOfExtZero_homKaehlerDerived (α : Ω(φ) ⟶ G) :
    homOfExtZero φ G (ShiftedHom.homEquiv (0 : ℤ) rfl
      (homKaehlerDerived φ G α)) = α := by
  unfold homOfExtZero
  erw [Equiv.symm_apply_apply]
  unfold homKaehlerDerived
  erw [(DerivedCategory.homologyFunctorFactors (SheafOfModules (ringSheaf J B))
    (0 : ℤ)).hom.naturality_assoc]
  erw [Iso.inv_hom_id_app_assoc]
  change (homologyZeroIso φ).inv ≫
    homologyMap (augmentation φ ≫ (CochainComplex.singleFunctor _ 0).map α) 0 ≫
      (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 G).hom = α
  erw [HomologicalComplex.homologyMap_comp, Category.assoc,
    singleObjHomologySelfIso_hom_naturality (ComplexShape.up ℤ) 0 α]
  erw [← Category.assoc (homologyMap (augmentation φ) 0)
    (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (Ω(φ))).hom α]
  exact (homologyZeroIso φ).inv_hom_id_assoc α

/-- An Ext⁰ class is determined by its induced map out of relative differentials. -/
theorem homOfExtZero_injective : Function.Injective (homOfExtZero φ G) := by
  intro e e' h
  apply (ShiftedHom.homEquiv (0 : ℤ) rfl).symm.injective
  apply sub_eq_zero.mp
  haveI : L(φ).IsStrictlyLE 0 := by
    unfold obj
    infer_instance
  apply derived_to_single_eq_zero_of_homology_map_eq_zero
  erw [Functor.map_sub, sub_eq_zero]
  let e₁ := (DerivedCategory.homologyFunctorFactors
    (SheafOfModules (ringSheaf J B)) 0).app L(φ) ≪≫ homologyZeroIso φ
  let e₂ := (DerivedCategory.homologyFunctorFactors
    (SheafOfModules (ringSheaf J B)) 0).app
      ((CochainComplex.singleFunctor _ 0).obj G) ≪≫
    singleObjHomologySelfIso (ComplexShape.up ℤ) 0 G
  apply (cancel_epi e₁.inv).1
  apply (cancel_mono e₂.hom).1
  dsimp only [e₁, e₂, Iso.trans_inv, Iso.trans_hom]
  calc
    _ = homOfExtZero φ G e := by
      exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)
    _ = homOfExtZero φ G e' := h
    _ = _ := by
      exact ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).symm

/-- The Ext⁰ identification `Hom(Ω(φ), G) ≃+ Ext⁽0⁾(Q L(φ), Q(G[0]))`. -/
def extZeroHomEquiv :
    (Ω(φ) ⟶ G) ≃+
      Ext⁽(0 : ℤ)⁾(DerivedCategory.Q.obj L(φ), coeffSingle G) where
  toFun α := ShiftedHom.homEquiv (0 : ℤ) rfl (homKaehlerDerived φ G α)
  invFun e := homOfExtZero φ G e
  left_inv := homOfExtZero_homKaehlerDerived φ G
  right_inv e := by
    apply homOfExtZero_injective φ G
    exact homOfExtZero_homKaehlerDerived φ G (homOfExtZero φ G e)
  map_add' α β := by
    change ShiftedHom.mk₀ (0 : ℤ) rfl (homKaehlerDerived φ G (α + β)) =
      ShiftedHom.mk₀ (0 : ℤ) rfl (homKaehlerDerived φ G α) +
        ShiftedHom.mk₀ (0 : ℤ) rfl (homKaehlerDerived φ G β)
    rw [← ShiftedHom.mk₀_add]
    congr 1
    unfold homKaehlerDerived
    erw [Functor.map_add, Preadditive.comp_add, Functor.map_add]

/-- The forward map of `extZeroHomEquiv` is `ShiftedHom.homEquiv` of `homKaehlerDerived`. -/
theorem extZeroHomEquiv_apply (α : Ω(φ) ⟶ G) :
    extZeroHomEquiv φ G α =
      ShiftedHom.homEquiv (0 : ℤ) rfl (homKaehlerDerived φ G α) :=
  rfl

end SheafOfModules.RingedSite.CotangentComplex
