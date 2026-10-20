module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-! # Locally Noetherian étale scheme charts -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An étale scheme chart of a locally Noetherian algebraic space has locally Noetherian
underlying scheme. -/
theorem isLocallyNoetherian_left_of_etaleChart {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X] {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] :
    AlgebraicGeometry.IsLocallyNoetherian U.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
