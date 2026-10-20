module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.Pushout
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RightAdjoint

/-! # Derived criterion for equivalence of coefficient pushout -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.SquareZeroAlgebraExtension

variable {S : Scheme.{u}}

/-- `DQ_X(ℱ) ⟶ DQ_X(𝒢)` is the image of ℱ ⟶ 𝒢 under the right adjoint of the inclusion
of `DerivedQCoh X` into `D(𝒪_X)`, after placing modules in degree zero. -/
def dqMap {X : AlgebraicSpace S} [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    (inclusion X).rightAdjoint.obj
        ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj ℱ) ⟶
      (inclusion X).rightAdjoint.obj
        ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj 𝒢) :=
  (inclusion X).rightAdjoint.map
    ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).map φ)

/-- `dqMap φ` is `(inclusion X).rightAdjoint` applied to the degree-zero image of φ. -/
theorem dqMap_eq {X : AlgebraicSpace S} [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    dqMap φ =
      (inclusion X).rightAdjoint.map
        ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).map φ) :=
  rfl

/-- For a quasi-compact and quasi-separated algebraic space, coefficient pushout is an
 equivalence whenever the degree-zero coefficient map becomes invertible under the
 right adjoint to the inclusion of complexes with quasi-coherent cohomology. -/
theorem pushout_isEquivalence {X B : AlgebraicSpace S} (f : X ⟶ B)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) [IsIso (dqMap φ)] :
    Functor.IsEquivalence (pushoutFunctor f φ) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.SquareZeroAlgebraExtension
