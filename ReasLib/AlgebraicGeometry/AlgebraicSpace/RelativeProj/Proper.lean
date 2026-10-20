module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.FiniteType

/-!
# Properness of relative projective spectra

A relative projective spectrum of a quasicoherent commutative graded algebra is proper
when its degree-zero module is finite and its algebra is of finite type over degree zero.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A morphism presented étale-locally by the projective spectrum of a quasicoherent
commutative graded algebra is proper if its degree-zero module is finite and the algebra
is of finite type over degree zero. -/
theorem proper_of_finiteType
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (deg : DegreePieces 𝒜) {P : AlgebraicSpace S} (π : P ⟶ X)
    (hπ : IsEtaleLocallyProj 𝒜 π) :
    (deg.obj 0).IsFiniteType ∧ FiniteTypeAsDegreeZeroAlgebra 𝒜 → Proper π := sorry

/-- A morphism presented étale-locally by the projective spectrum of a quasicoherent
commutative graded algebra is proper if its degree-zero module is finite and the algebra
is of finite type over the base. -/
theorem proper_of_finiteTypeAsBase
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (deg : DegreePieces 𝒜) {P : AlgebraicSpace S} (π : P ⟶ X)
    (hπ : IsEtaleLocallyProj 𝒜 π) :
    (deg.obj 0).IsFiniteType ∧ FiniteTypeAsBaseAlgebra 𝒜 → Proper π := by
  intro h
  exact proper_of_finiteType 𝒜 hqc deg π hπ ((finiteTypeConditions_iff 𝒜 hqc deg).mpr h)

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
