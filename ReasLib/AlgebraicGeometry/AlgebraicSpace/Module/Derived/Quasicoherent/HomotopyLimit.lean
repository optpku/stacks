module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RightAdjoint

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- The coherator carries an ambient homotopy limit of a sequential inverse system of
quasi-coherent sheaves to its homotopy limit in `DerivedQCoh X`. -/
theorem rightAdjoint_isHomotopyLimit
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (F : SequentialInverseSystem (QCoh X)) (K : ModuleDerived X)
    (hK : HomotopyLimit.IsOf
      (F ⋙ QCoh.inclusion X ⋙ DerivedCategory.singleFunctor (Modules X) (0 : ℤ)) K) :
    HomotopyLimit.IsOf
      (F ⋙ QCoh.inclusion X ⋙ DerivedCategory.singleFunctor (Modules X) (0 : ℤ) ⋙
        (inclusion X).rightAdjoint)
      ((inclusion X).rightAdjoint.obj K) :=
  sorry

/-- An ambient homotopy limit of a sequential inverse system of quasi-coherent sheaves has
affine-étale hypercohomology only in degrees `0` and `1`. -/
theorem homotopyLimit_affineEtaleHypercohomology_isZero
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (F : SequentialInverseSystem (QCoh X)) (K : ModuleDerived X)
    (hK : HomotopyLimit.IsOf
      (F ⋙ QCoh.inclusion X ⋙ DerivedCategory.singleFunctor (Modules X) (0 : ℤ)) K)
    {U : AlgebraicSpace S} (φ : U ⟶ X) [IsAffine U] [Etale φ]
    (i : ℤ) (hi : i ∉ Set.Icc (0 : ℤ) 1) :
    IsZero (cohomologyAb U ((restrictFunctorDerived φ).obj K) i) :=
  sorry

/-- The coherator of an ambient homotopy limit of a sequential inverse system of
quasi-coherent sheaves is bounded above and has vanishing cohomology sheaves in
negative degrees. -/
theorem rightAdjoint_homotopyLimit_isBounded
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (F : SequentialInverseSystem (QCoh X)) (K : ModuleDerived X)
    (hK : HomotopyLimit.IsOf
      (F ⋙ QCoh.inclusion X ⋙ DerivedCategory.singleFunctor (Modules X) (0 : ℤ)) K) :
    ((inclusion X).rightAdjoint.obj K).obj.IsGE 0 ∧
      DerivedCategory.IsBoundedAbove ((inclusion X).rightAdjoint.obj K).obj :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
