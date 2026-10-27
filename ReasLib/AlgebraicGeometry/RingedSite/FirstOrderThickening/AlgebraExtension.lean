/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.Split
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.IsoClass

/-!
# Classification of square-zero algebra extensions on a ringed site

The obstruction difference from the split extension identifies isomorphism classes of
square-zero algebra extensions with degree-one Ext of the relative naive cotangent complex.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open SheafOfModules.RingedSite.FirstOrderThickening.Solution
open SheafOfModules.RingedSite.NaiveCotangent
open scoped DerivedExt SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace Solution

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, and Ext must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O_B O : Sheaf J CommRingCat.{u}}
variable (fSharp : O_B ⟶ O)
variable (G : SheafOfModules (ringSheaf J O))

/-- The canonical class of a square-zero algebra extension is its obstruction difference
from the split extension. -/
def extensionClass
    (p : IsoClass (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G)) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  Solution.vsub p (isoClassMk (trivialSolution fSharp G))

/-- The class of a represented extension is the obstruction from the split solution
to that representative. -/
theorem extensionClass_mk
    (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G)) :
    extensionClass fSharp G (isoClassMk S) = obstruction (trivialSolution fSharp G) S := sorry

/-- The obstruction class gives a bijection from square-zero algebra extensions with
identified kernel to degree-one Ext of the relative naive cotangent complex. -/
theorem extensionClass_bijective : Function.Bijective (extensionClass fSharp G) := sorry

/-- Degree-one Ext of the relative naive cotangent complex classifies square-zero algebra
extensions with identified kernel, by the inverse of the canonical obstruction-class map. -/
def extensionEquiv :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)) ≃
      IsoClass (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G) :=
  (Equiv.ofBijective (extensionClass fSharp G) (extensionClass_bijective fSharp G)).symm

/-- The extension corresponding to an Ext class has that canonical obstruction class. -/
theorem extensionClass_extensionEquiv
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))) :
    extensionClass fSharp G (extensionEquiv fSharp G ξ) = ξ := sorry

/-- The inverse of the classification equivalence is the canonical obstruction-class map. -/
theorem extensionEquiv_symm_apply
    (p : IsoClass (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G)) :
    (extensionEquiv fSharp G).symm p = extensionClass fSharp G p := sorry

/-- The zero Ext class corresponds to the split square-zero extension. -/
theorem extensionEquiv_zero :
    extensionEquiv fSharp G 0 = isoClassMk (trivialSolution fSharp G) := sorry

/-- An extension corresponds to a given Ext class exactly when its canonical obstruction
class equals that Ext class. -/
theorem extensionEquiv_apply_eq_iff
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)))
    (p : IsoClass (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G)) :
    extensionEquiv fSharp G ξ = p ↔ extensionClass fSharp G p = ξ := sorry

/-- The canonical class vanishes exactly for the split extension class. -/
theorem extensionClass_eq_zero_iff
    (p : IsoClass (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G)) :
    extensionClass fSharp G p = 0 ↔ p = isoClassMk (trivialSolution fSharp G) := sorry

end Solution
end SheafOfModules.RingedSite.FirstOrderThickening
