module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Admissible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Two finite-type separated algebraic spaces over a quasi-compact
quasi-separated base containing the same finite-type separated open subspace
admit blowups admissible over that open subspace which embed openly into a
common finite-type separated algebraic space over the base, with all maps
from the common open subspace and to the base commuting. -/
theorem exists_isAdmissibleBlowup_isOpenImmersion
    {S : Scheme.{u}} {Y U X1 X2 : AlgebraicSpace S}
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f1 : X1 ⟶ Y) (f2 : X2 ⟶ Y) (fU : U ⟶ Y)
    [FiniteType f1] [FiniteType f2] [FiniteType fU]
    [Separated f1] [Separated f2] [Separated fU]
    (ι1 : U ⟶ X1) (ι2 : U ⟶ X2)
    [IsOpenImmersion ι1] [IsOpenImmersion ι2]
    (hι1 : ι1 ≫ f1 = fU) (hι2 : ι2 ≫ f2 = fU) :
    ∃ (X1' X2' X : AlgebraicSpace S)
      (b1 : X1' ⟶ X1) (b2 : X2' ⟶ X2)
      (j1 : X1' ⟶ X) (j2 : X2' ⟶ X) (pX : X ⟶ Y)
      (u1' : U ⟶ X1') (u2' : U ⟶ X2') (uX : U ⟶ X),
      IsAdmissibleBlowup (OpenSubspace.ofι ι1) b1 ∧
        IsAdmissibleBlowup (OpenSubspace.ofι ι2) b2 ∧
        IsOpenImmersion j1 ∧ IsOpenImmersion j2 ∧
        FiniteType pX ∧ Separated pX ∧
        u1' ≫ b1 = ι1 ∧ u2' ≫ b2 = ι2 ∧
        u1' ≫ j1 = uX ∧ u2' ≫ j2 = uX ∧
        j1 ≫ pX = b1 ≫ f1 ∧ j2 ≫ pX = b2 ≫ f2 ∧
        uX ≫ pX = fU :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
