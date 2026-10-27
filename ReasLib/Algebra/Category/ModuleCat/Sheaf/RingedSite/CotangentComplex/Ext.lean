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

/-- The naive-to-derived Ext¹ comparison of `(NaiveCotangent.obj A (Under.mk φ))` with `L(φ)`. -/
def extOneTruncEquiv :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj A (Under.mk φ)), coeffSingle G) ≃+
      Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj L(φ), coeffSingle G) where
  toFun ξ :=
    ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toNaiveDerived φ)) ξ (add_zero (1 : ℤ))
  invFun η := fromDerivedToNaiveExt φ G η
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- The forward map of `extOneTruncEquiv` is precomposition along `toNaiveDerived`. -/
theorem extOneTruncEquiv_apply
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj A (Under.mk φ)), coeffSingle G)) :
    extOneTruncEquiv φ G ξ =
      ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (toNaiveDerived φ)) ξ
        (add_zero (1 : ℤ)) :=
  sorry

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

/-- The Ext⁰ identification `Hom(Ω(φ), G) ≃+ Ext⁽0⁾(Q L(φ), Q(G[0]))`. -/
def extZeroHomEquiv :
    (Ω(φ) ⟶ G) ≃+
      Ext⁽(0 : ℤ)⁾(DerivedCategory.Q.obj L(φ), coeffSingle G) where
  toFun α := ShiftedHom.homEquiv (0 : ℤ) rfl (homKaehlerDerived φ G α)
  invFun e := homOfExtZero φ G e
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- The forward map of `extZeroHomEquiv` is `ShiftedHom.homEquiv` of `homKaehlerDerived`. -/
theorem extZeroHomEquiv_apply (α : Ω(φ) ⟶ G) :
    extZeroHomEquiv φ G α =
      ShiftedHom.homEquiv (0 : ℤ) rfl (homKaehlerDerived φ G α) :=
  sorry

end SheafOfModules.RingedSite.CotangentComplex
