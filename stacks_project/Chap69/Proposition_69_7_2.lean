module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.AffineCover
import StacksCheckRecall

/-!
# Proposition 69.7.2

Vanishing of étale cohomology of quasi-coherent modules on a quasi-compact
separated algebraic space in degrees at least the fibre cardinality of a
surjective étale cover by an affine scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Proposition 69.7.2: étale cohomology of a quasi-coherent module on a
quasi-compact separated algebraic space vanishes in degrees at least the
cardinality of the fibres of a surjective étale morphism from an affine scheme. -/
@[stacks 072B] #check
  (AlgebraicGeometry.AlgebraicSpace.cohomology_isZero_of_fibre_encard_le :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    [IsQuasiCompact X] [IsAbsolutelySeparated X] [AlgebraicGeometry.IsAffine U.left]
    (f : ofOver U ⟶ X) [Etale f] [Surjective f]
    (d : ℕ) (hd : ∀ x : Points X, (Points.mapOfOver f ⁻¹' {x}).encard ≤ d)
    (F : X.Modules) [F.IsQuasicoherent] {q : ℕ} (hq : d ≤ q)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})],
    IsZero (cohomology X F q))

/- Étale cohomology of a quasi-coherent module vanishes in degrees at least `d`
when an affine étale cover has field-valued fibre degrees bounded by `d`. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.cohomology_isZero_of_degreesOfFibresBoundedBy :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    [IsQuasiCompact X] [IsAbsolutelySeparated X] [AlgebraicGeometry.IsAffine U.left]
    (f : ofOver U ⟶ X) [Etale f] [Surjective f]
    (d : ℕ) (hd : degreesOfFibresBoundedBy f d)
    (F : X.Modules) [F.IsQuasicoherent] {q : ℕ} (hq : d ≤ q)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})],
    IsZero (cohomology X F q))

end AlgebraicGeometry.AlgebraicSpace
