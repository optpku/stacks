module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed

/-!
# Universal closedness of relative projective spectra

Relative Proj is universally closed when the structure map to degree zero is integral
and the graded algebra is of finite type over degree zero.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- A morphism étale-locally presented by the canonical projective-spectrum morphisms
of a quasicoherent commutative graded algebra sheaf is universally closed if the structure
map to degree zero is integral and the algebra is of finite type over degree zero. -/
theorem universallyClosed_of_integralDegreeZero
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    {P : AlgebraicSpace S} (π : P ⟶ X)
    (hπ : IsEtaleLocallyProj 𝒜 π)
    (hIntegral : IntegralDegreeZeroAlgebra 𝒜)
    (hFiniteType : FiniteTypeAsDegreeZeroAlgebra 𝒜) :
    AlgebraicSpace.UniversallyClosed π := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
