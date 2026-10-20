/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.Locus.FiniteTypeCounterexample
import StacksCheckRecall

open CategoryTheory
open scoped FittingIdeal

#check (AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing : Type)

#check (AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.finiteSupportIdeal :
  Ideal AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing)

#check (AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.mem_finiteSupportIdeal_iff :
  ∀ {a : AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing},
    a ∈ AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.finiteSupportIdeal ↔
      {n : ℕ | a n ≠ 0}.Finite)

#check
  (AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.exists_maximalIdeal_containing_finiteSupportIdeal :
    ∃ m : Ideal AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing,
      m.IsMaximal ∧
        AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.finiteSupportIdeal ≤ m)

#check (isAbsolutelyFlatRing_pi (fun _ : ℕ ↦ ZMod 2) :
  IsAbsolutelyFlatRing AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing)

#check (AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.sheaf :
  ∀ _ : Ideal AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing,
    AlgebraicGeometry.BinarySequenceSpectrum.spectrum.Modules)

#check (Module.Finite.quotient
  AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing :
  ∀ m : Ideal AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing,
    Module.Finite AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing
      (AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing ⧸ m))

#check (AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.sheafIsFiniteType :
  ∀ m : Ideal AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing,
    (AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.sheaf m).IsFiniteType)

#check (AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.sheafIsFlat :
  ∀ m : Ideal AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing,
    SheafOfModules.IsFlat
      (AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.sheaf m))

#check (FittingIdeal.quotientAtZero :
  ∀ m : Ideal AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing,
    Fit[AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing]_(0)(AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing ⧸ m) = m)

#check (AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.fittingIdeal_succ_eq_top :
  ∀ (m : Ideal AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing) (i : ℕ),
    Fit[AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing]_(i + 1)(AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing ⧸ m) = ⊤)

#check
  (AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.fittingIdealSheaf_zero_eq_quotientMap_ker :
    ∀ m : Ideal AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing,
      AlgebraicGeometry.Scheme.fittingIdealSheaf
          (AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.sheaf m) 0 =
        (AlgebraicGeometry.Spec.quotientMap
          (R := CommRingCat.of AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing) m :
          AlgebraicGeometry.Spec
              (CommRingCat.of (AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing ⧸ m)) ⟶
            AlgebraicGeometry.BinarySequenceSpectrum.spectrum).ker)

#check
  (AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.fittingIdealSheaf_succ_eq_top :
    ∀ (m : Ideal AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing) (i : ℕ),
      AlgebraicGeometry.Scheme.fittingIdealSheaf
          (AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.sheaf m) (i + 1) = ⊤)

#check
  (AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.point_not_isOpen_singleton :
    ∀ (m : Ideal AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing)
        (hm : m.IsMaximal)
        (_ : AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.finiteSupportIdeal ≤ m),
      ¬ IsOpen
        ({AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.point m hm} :
          Set AlgebraicGeometry.BinarySequenceSpectrum.spectrum))

#check
  (AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.identity_not_factor_through_openClosedLocus :
    ∀ (m : Ideal AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing)
        (hm : m.IsMaximal)
        (_ : AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.finiteSupportIdeal ≤ m),
      ¬ Nonempty
        (Over.mk (𝟙 AlgebraicGeometry.BinarySequenceSpectrum.spectrum) ⟶
          Over.mk
            (AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.openClosedLocusι m hm)))

/- Example 31.9.8: the identity of the binary-sequence spectrum does not factor through the
Fitting flat locus of the associated finite-type flat quotient sheaf. -/
@[stacks 0FJ0] #check
  (AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.identity_not_factor_through_fittingFlatLocus :
    ∀ (m : Ideal AlgebraicGeometry.BinarySequenceSpectrum.CoordinateRing)
        (_ : m.IsMaximal)
        (_ : AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.finiteSupportIdeal ≤ m),
      ¬ Nonempty
        (Over.mk (𝟙 AlgebraicGeometry.BinarySequenceSpectrum.spectrum) ⟶
          Over.mk (AlgebraicGeometry.Scheme.fittingFlatLocusι
            (AlgebraicGeometry.Scheme.FittingIdealFiniteTypeCounterexample.sheaf m))))
