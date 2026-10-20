module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FibrePower.OffDiagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.OffDiagonal

/-! # Off-diagonal fibre products and permutation actions -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.offDiagonalPermLift :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X) [Separated f] (n : ℕ),
    ULift.{u} (Equiv.Perm (Fin n)) →* Aut (offDiagonal f n))
