/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Preservation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Coherator.Boundedness
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Coherator.Exact

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The coherator carries an ambient homotopy limit of a sequential inverse system of
quasi-coherent sheaves to its homotopy limit in `DerivedQCoh X`. -/
theorem rightAdjoint_isHomotopyLimit
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (F : SequentialInverseSystem (Scheme.QCoh X))
    (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (hK : HomotopyLimit.IsOf
      (F ⋙ Scheme.QCoh.inclusion X ⋙
        DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)) K) :
    HomotopyLimit.IsOf
      (F ⋙ Scheme.QCoh.inclusion X ⋙
        DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ) ⋙
        (Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint)
      ((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint.obj K) := sorry

/-- An ambient homotopy limit of a sequential inverse system of quasi-coherent sheaves has
affine-open hypercohomology only in degrees `0` and `1`. -/
theorem homotopyLimit_affineHypercohomology_isZero
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (F : SequentialInverseSystem (Scheme.QCoh X))
    (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (hK : HomotopyLimit.IsOf
      (F ⋙ Scheme.QCoh.inclusion X ⋙
        DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)) K)
    (U : X.Opens) (hU : IsAffineOpen U) (i : ℤ) (hi : i ∉ Set.Icc (0 : ℤ) 1) :
    IsZero (RingedSpace.moduleOpenHypercohomology X.toRingedSpace U K i) := sorry

/-- The coherator of an ambient homotopy limit of a sequential inverse system of
quasi-coherent sheaves is bounded below and bounded above. -/
theorem rightAdjoint_homotopyLimit_isBounded
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (F : SequentialInverseSystem (Scheme.QCoh X))
    (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (hK : HomotopyLimit.IsOf
      (F ⋙ Scheme.QCoh.inclusion X ⋙
        DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)) K) :
    DerivedCategory.IsBoundedBelow
        ((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint.obj K).obj ∧
      DerivedCategory.IsBoundedAbove
        ((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint.obj K).obj := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
