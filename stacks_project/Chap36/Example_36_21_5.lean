/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Coherator.HomotopyLimit

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Example 36.21.5 (1): the coherator carries an ambient homotopy limit of a sequential
inverse system of quasi-coherent sheaves to its homotopy limit in `DerivedQCoh X`. -/
@[stacks 0CSB] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.rightAdjoint_isHomotopyLimit :
    ∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
      (F : SequentialInverseSystem (Scheme.QCoh X))
      (K : RingedSpace.ModuleDerived X.toRingedSpace),
      HomotopyLimit.IsOf
          (F ⋙ Scheme.QCoh.inclusion X ⋙
            DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)) K →
        HomotopyLimit.IsOf
          (F ⋙ Scheme.QCoh.inclusion X ⋙
            DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ) ⋙
            (Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint)
          ((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint.obj K))

/- Example 36.21.5 (2): an ambient homotopy limit of a sequential inverse system of
quasi-coherent sheaves has affine-open hypercohomology only in degrees `0` and `1`. -/
@[stacks 0CSB] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.homotopyLimit_affineHypercohomology_isZero :
    ∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
      (F : SequentialInverseSystem (Scheme.QCoh X))
      (K : RingedSpace.ModuleDerived X.toRingedSpace),
      HomotopyLimit.IsOf
          (F ⋙ Scheme.QCoh.inclusion X ⋙
            DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)) K →
        ∀ (U : X.Opens), IsAffineOpen U → ∀ i : ℤ, i ∉ Set.Icc (0 : ℤ) 1 →
          IsZero (RingedSpace.moduleOpenHypercohomology X.toRingedSpace U K i))

/- Example 36.21.5 (3): the coherator of an ambient homotopy limit of a sequential inverse
system of quasi-coherent sheaves is bounded below and bounded above. -/
@[stacks 0CSB] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.rightAdjoint_homotopyLimit_isBounded :
    ∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
      (F : SequentialInverseSystem (Scheme.QCoh X))
      (K : RingedSpace.ModuleDerived X.toRingedSpace),
      HomotopyLimit.IsOf
          (F ⋙ Scheme.QCoh.inclusion X ⋙
            DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)) K →
        DerivedCategory.IsBoundedBelow
            ((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint.obj K).obj ∧
          DerivedCategory.IsBoundedAbove
            ((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint.obj K).obj)

end AlgebraicGeometry.Scheme.DerivedQCoh
