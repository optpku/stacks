module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Proper
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj SheafOfModules.RingedSite

universe u

/- Lemma 71.11.10. For a quasicoherent commutative graded algebra sheaf, finite type over
degree zero and over the base are equivalent under the common finite-module condition on
degree zero. Under these conditions its relative projective-spectrum morphism is proper. -/
@[stacks 084I] #check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.finiteTypeConditions_iff :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (deg : DegreePieces 𝒜),
    ((deg.obj 0).IsFiniteType ∧ FiniteTypeAsDegreeZeroAlgebra 𝒜) ↔
      ((deg.obj 0).IsFiniteType ∧ FiniteTypeAsBaseAlgebra 𝒜))

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.proper_of_finiteType :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (deg : DegreePieces 𝒜) {P : AlgebraicSpace S} (π : P ⟶ X)
    (hπ : IsEtaleLocallyProj 𝒜 π),
    (deg.obj 0).IsFiniteType ∧ FiniteTypeAsDegreeZeroAlgebra 𝒜 → Proper π)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.proper_of_finiteTypeAsBase :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (deg : DegreePieces 𝒜) {P : AlgebraicSpace S} (π : P ⟶ X)
    (hπ : IsEtaleLocallyProj 𝒜 π),
    (deg.obj 0).IsFiniteType ∧ FiniteTypeAsBaseAlgebra 𝒜 → Proper π)
