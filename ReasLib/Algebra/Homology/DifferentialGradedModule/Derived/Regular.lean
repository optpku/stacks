module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Generator
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Hom
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Equiv
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Self-Extensions of the Regular Derived DG Module

The cohomology of a cochain differential graded algebra is canonically the shifted self-Hom of
its regular object in the derived category.  This leaf exposes the comparison map independently
of any tensor realization, together with the bijectivity and bundled-equivalence interfaces used
by derived Morita arguments.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule.Derived

variable {R : Type u} [CommRing R]

/-- Every shift of the regular DG module is K-projective. -/
@[stacks 09K1 "K-projectivity of shifts of the regular DG module"]
theorem regularShift_kProjective (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    DifferentialGradedModule.Homotopy.kProjective A
      (CochainDGAlgebra.RegularModule.shiftK A n) := sorry

/-- The underlying cohomology of the regular DG module is canonically the cohomology of the
cochain DGA itself. -/
@[stacks 09LZ "cohomology of the regular DG module"]
noncomputable def regularHomologyIso (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    A.regularModule.homology n ≅ A.homology n :=
  (HomologicalComplex.homologyFunctor
    (ModuleCat.{v} R) (ComplexShape.up ℤ) n).mapIso
      (eqToIso (CochainDGAlgebra.regularModule_toCochainComplex A))

/-- A cohomology class of `A` determines the corresponding homotopy morphism from the
oppositely shifted regular DG module to the unshifted regular DG module. -/
@[stacks 09LZ "regular homotopy morphism from a cohomology class"]
noncomputable def regularHomotopyOfCohomology
    (A : CochainDGAlgebra.{u, v} R) (n : ℤ) (x : A.homology n) :
    CochainDGAlgebra.RegularModule.shiftK A (-n) ⟶
      (DifferentialGradedModule.toK A).obj A.regularModule :=
  CochainDGAlgebra.RegularModule.homotopyOfHomology A A.regularModule (-n)
    (ModuleCat.Hom.hom (regularHomologyIso A (- -n)).inv
      (ModuleCat.Hom.hom
        (eqToIso (congrArg (fun k : ℤ ↦ A.homology k)
          (Int.neg_neg n).symm)).hom x))

/-- Shifting the regular derived object by `n` agrees with localizing the explicitly shifted
regular DG module. -/
@[stacks 09LZ "shift of the regular derived DG module"]
noncomputable def regularShiftIso (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    (regularObject A)⟦n⟧ ≅
      (Q A).obj (CochainDGAlgebra.RegularModule.shiftK A n) :=
  (shiftFunctor _ n).mapIso ((Q A).mapIso (regularZeroIso A)) ≪≫
    (toKShiftIso A.regularModule n).symm

/-- The canonical map from `Hⁿ(A)` to degree-`n` self-extensions of the regular object.  A
cohomology class acts on the shifted unit, is localized, and is then transported across the
canonical shift identifications. -/
@[stacks 09LZ "cohomology of a DGA as regular self-Ext"]
noncomputable def regularSelfExtLinearMap (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    A.homology n →ₗ[R] ShiftedHom (regularObject A) (regularObject A) n where
  toFun x :=
    (ShiftedHom.sourceShiftEquiv (regularObject A) (regularObject A) n).symm
      ((regularShiftIso A (-n)).hom ≫
        (Q A).map (regularHomotopyOfCohomology A n x) ≫
        ((Q A).mapIso (regularZeroIso A)).inv)
  map_add' := sorry
  map_smul' := sorry

/-- Evaluation of `regularSelfExtLinearMap` is the localized action of a chosen cycle
representing the cohomology class. -/
@[stacks 09LZ "regular self-Ext map evaluation", simp]
theorem regularSelfExtLinearMap_apply (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    (x : A.homology n) :
    regularSelfExtLinearMap A n x =
      (ShiftedHom.sourceShiftEquiv (regularObject A) (regularObject A) n).symm
        ((regularShiftIso A (-n)).hom ≫
          (Q A).map (regularHomotopyOfCohomology A n x) ≫
          ((Q A).mapIso (regularZeroIso A)).inv) := sorry

/-- Cohomology of a cochain DGA maps bijectively to the shifted self-Homs of its regular
derived object. -/
@[stacks 09LZ "regular self-Ext comparison is bijective"]
theorem regularSelfExtLinearMap_bijective
    (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    Function.Bijective (regularSelfExtLinearMap A n) := sorry

/-- The canonical bundled linear equivalence from DGA cohomology to regular self-Ext. -/
@[stacks 09LZ "regular self-Ext linear equivalence"]
noncomputable def regularSelfExtLinearEquiv
    (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    A.homology n ≃ₗ[R] ShiftedHom (regularObject A) (regularObject A) n :=
  LinearEquiv.ofBijective (regularSelfExtLinearMap A n)
    (regularSelfExtLinearMap_bijective A n)

/-- A bundled linear equivalence from DGA cohomology to regular self-Ext, using an explicit
bijectivity certificate when a downstream construction has one available. -/
@[stacks 09LZ "certificate-based regular self-Ext linear equivalence"]
noncomputable def regularSelfExtLinearEquivOfBijective
    (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    (h : Function.Bijective (regularSelfExtLinearMap A n)) :
    A.homology n ≃ₗ[R] ShiftedHom (regularObject A) (regularObject A) n :=
  LinearEquiv.ofBijective (regularSelfExtLinearMap A n) h

/-- The forward map of `regularSelfExtLinearEquiv` is the canonical regular self-Ext map. -/
@[stacks 09LZ "regular self-Ext linear equivalence evaluation", simp]
theorem regularSelfExtLinearEquiv_apply
    (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    (x : A.homology n) :
    regularSelfExtLinearEquiv A n x = regularSelfExtLinearMap A n x := sorry

/-- The forward map of the certificate-based regular self-Ext equivalence. -/
@[stacks 09LZ "certificate-based regular self-Ext equivalence evaluation", simp]
theorem regularSelfExtLinearEquivOfBijective_apply
    (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    (h : Function.Bijective (regularSelfExtLinearMap A n)) (x : A.homology n) :
    regularSelfExtLinearEquivOfBijective A n h x = regularSelfExtLinearMap A n x := sorry

end DifferentialGradedModule.Derived
