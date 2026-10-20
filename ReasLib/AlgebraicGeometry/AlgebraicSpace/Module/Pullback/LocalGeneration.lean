module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage

/-!
# Finite type under module pullback

Pullback along a morphism of algebraic spaces preserves finite-type module sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The pullback of a finite-type module sheaf along any morphism of algebraic spaces is of
finite type. -/
instance pullback_isFiniteType {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (F : X.Modules) [F.IsFiniteType] : ((pullback f).obj F).IsFiniteType :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
