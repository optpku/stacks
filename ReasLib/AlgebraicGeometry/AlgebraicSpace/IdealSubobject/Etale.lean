module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Product

/-!
# Pushing finite type ideals along étale morphisms

A finite type quasi-coherent ideal along a quasi-compact separated étale morphism
divides the pullback of a finite type quasi-coherent ideal on the target, with
control of its vanishing locus away from a quasi-compact open subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`,
and let `φ : W ⟶ X` be a quasi-compact separated étale morphism. If a finite type
quasi-coherent ideal `I` on `W` has vanishing locus disjoint from the preimage of a
quasi-compact open subspace `U` of `X`, then there is a finite type quasi-coherent
ideal `J` on `X` whose vanishing locus avoids `U` and whose pullback is `I * I'`
for some finite type quasi-coherent ideal `I'` on `W`. -/
theorem exists_finiteTypeIdeal_mul_of_etale {S : Scheme.{u}}
    {W X : AlgebraicSpace S} [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (φ : W ⟶ X) [QuasiCompact φ] [Separated φ] [Etale φ]
    (U : OpenSubspace X) [IsQuasiCompact U.X] (I : IdealSubobject W)
    [IsQuasiCoherent I] [(I : W.Modules).IsFiniteType]
    (hI : Disjoint (ClosedSubspace.ofQuasiCoherentIdeal I).pointsSet
      (Points.map φ ⁻¹' U.pointsSet)) :
    ∃ (J : IdealSubobject X) (_ : IsQuasiCoherent J),
      (J : X.Modules).IsFiniteType ∧
        Disjoint (ClosedSubspace.ofQuasiCoherentIdeal J).pointsSet U.pointsSet ∧
          ∃ (I' : IdealSubobject W) (_ : IsQuasiCoherent I'),
            (I' : W.Modules).IsFiniteType ∧
              J.pullback φ = IdealSubobject.mul I I' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
