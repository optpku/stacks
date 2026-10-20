module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Basic
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Formal algebraic spaces as fpqc sheaves

Formal algebraic spaces satisfy fpqc descent, including the singleton sheaf
condition for faithfully flat morphisms of affine schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A formal algebraic space over a scheme `S` is a sheaf for the fpqc topology
on schemes over `S`. -/
@[stacks 0AQD]
theorem isSheaf_fpqc {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) X :=
  sorry

/-- The functor of points of a formal algebraic space satisfies the singleton
sheaf condition for every faithfully flat morphism of affine schemes over `S`. -/
theorem isSheafFor_affineFaithfullyFlat {S : Scheme.{u}}
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    {T T' : Over S} (f : T' ⟶ T)
    [IsAffine T.left] [IsAffine T'.left] [Flat f.left] [Surjective f.left] :
    Presieve.IsSheafFor X (Presieve.singleton f) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
