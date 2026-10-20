/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.HomotopyLimit
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/- Example 75.19.5 (1): the coherator carries an ambient homotopy limit of a sequential
inverse system of quasi-coherent sheaves to its homotopy limit in `DerivedQCoh X`. -/
@[stacks 0CST] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.rightAdjoint_isHomotopyLimit :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (F : SequentialInverseSystem (QCoh X)) (K : ModuleDerived X),
      HomotopyLimit.IsOf
          (F ⋙ QCoh.inclusion X ⋙
            DerivedCategory.singleFunctor (Modules X) (0 : ℤ)) K →
        HomotopyLimit.IsOf
          (F ⋙ QCoh.inclusion X ⋙
            DerivedCategory.singleFunctor (Modules X) (0 : ℤ) ⋙
            (inclusion X).rightAdjoint)
          ((inclusion X).rightAdjoint.obj K))

/- Example 75.19.5 (2): an ambient homotopy limit of a sequential inverse system of
quasi-coherent sheaves has affine-étale hypercohomology only in degrees `0` and `1`. -/
@[stacks 0CST] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.homotopyLimit_affineEtaleHypercohomology_isZero :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (F : SequentialInverseSystem (QCoh X)) (K : ModuleDerived X),
      HomotopyLimit.IsOf
          (F ⋙ QCoh.inclusion X ⋙
            DerivedCategory.singleFunctor (Modules X) (0 : ℤ)) K →
        ∀ {U : AlgebraicSpace S} (φ : U ⟶ X) [IsAffine U] [Etale φ],
          ∀ i : ℤ, i ∉ Set.Icc (0 : ℤ) 1 →
            IsZero (cohomologyAb U ((restrictFunctorDerived φ).obj K) i))

/- Example 75.19.5 (3): the coherator of an ambient homotopy limit of a sequential inverse
system of quasi-coherent sheaves lies in `Dᵇ_QCoh` and has vanishing cohomology sheaves in
negative degrees. -/
@[stacks 0CST] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.rightAdjoint_homotopyLimit_isBounded :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (F : SequentialInverseSystem (QCoh X)) (K : ModuleDerived X),
      HomotopyLimit.IsOf
          (F ⋙ QCoh.inclusion X ⋙
            DerivedCategory.singleFunctor (Modules X) (0 : ℤ)) K →
        ((inclusion X).rightAdjoint.obj K).obj.IsGE 0 ∧
          DerivedCategory.IsBoundedAbove ((inclusion X).rightAdjoint.obj K).obj)

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
