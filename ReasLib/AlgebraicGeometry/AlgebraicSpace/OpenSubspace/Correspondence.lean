module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction

/-! # Open subspaces and open sets of points -/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.OpenSubspace

/-- Every open set of points is the point set of an open subspace, unique up to unique lift. -/
theorem exists_of_isOpen {S : Scheme.{u}} {X : AlgebraicSpace S}
    (W : Set (Points X)) (hW : IsOpen W) :
    ∃ U : OpenSubspace X, U.pointsSet = W ∧
      ∀ V : OpenSubspace X, V.pointsSet = W → ∃! f : V.X ⟶ U.X, f ≫ U.ι = V.ι :=
  ⟨fromOpens ⟨W, hW⟩, fromOpens_pointsSet _, sorry⟩

end AlgebraicGeometry.AlgebraicSpace.OpenSubspace
