module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.CodimensionZero
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite

/-!
# Quasi-finiteness over a codimension-zero point

For a locally finite type morphism of algebraic spaces, the fibre over a
codimension-zero point of the target consists of codimension-zero points of the
source if and only if the morphism is quasi-finite at every point of that
fibre, equivalently at every codimension-zero point of the fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finite type morphism of algebraic spaces has a fibrewise
quasi-finiteness criterion over each codimension-zero point of its target. -/
theorem tfae_fiber_subset_codimZero_quasiFiniteAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {y : Points Y} (hy : y ∈ codimZeroPoints Y) :
    List.TFAE
      [ Points.map f ⁻¹' {y} ⊆ codimZeroPoints X
      , ∀ x : Points X, Points.map f x = y → FiniteType.QuasiFiniteAt f x
      , ∀ x : Points X,
          x ∈ codimZeroPoints X → Points.map f x = y → FiniteType.QuasiFiniteAt f x ] :=
  sorry

/-- A fibre over a codimension-zero target point consists of codimension-zero
points exactly when the morphism is quasi-finite at every point of the fibre. -/
theorem fiber_subset_codimZero_iff_quasiFiniteAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {y : Points Y} (hy : y ∈ codimZeroPoints Y) :
    Points.map f ⁻¹' {y} ⊆ codimZeroPoints X ↔
      ∀ x : Points X, Points.map f x = y → FiniteType.QuasiFiniteAt f x :=
  sorry

/-- Over a codimension-zero target point, quasi-finiteness on the whole fibre is
equivalent to quasi-finiteness on its codimension-zero points. -/
theorem quasiFiniteAt_fiber_iff_quasiFiniteAt_codimZero {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {y : Points Y} (hy : y ∈ codimZeroPoints Y) :
    (∀ x : Points X, Points.map f x = y → FiniteType.QuasiFiniteAt f x) ↔
      ∀ x : Points X,
        x ∈ codimZeroPoints X → Points.map f x = y → FiniteType.QuasiFiniteAt f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
