module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Pullback

/-!
# Proper diagrams covering a gerbe locus

A separated finite-type morphism from an algebraic stack to a quasi-compact,
quasi-separated algebraic space admits a proper diagram covering any
quasi-compact open over which it is a gerbe.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A separated finite-type morphism from an algebraic stack to a quasi-compact,
absolutely quasi-separated algebraic space, which is a gerbe over a quasi-compact
open subspace, admits a commutative diagram of algebraic spaces `Z ⟶ Zbar ⟶ Y`
and a morphism `Z.toGroupoids ⟶ X` over `Y`, where `Z ⟶ Zbar` is an open
immersion, `Zbar ⟶ Y` and `Z.toGroupoids ⟶ X` are proper, and the image of
`Z ⟶ Y` contains the given open subspace. The triangle through the stack
commutes up to a 2-isomorphism. -/
@[stacks 0CQ7]
theorem exists_isOpenImmersion_proper_covering_open
    {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [AlgebraicSpace.IsQuasiCompact Y]
    [AlgebraicSpace.IsAbsolutelyQuasiSeparated Y]
    {X : GroupoidsOver S} [AlgebraicStack X] (f : X ⟶ Y.toGroupoids)
    [AlgebraicStack.Separated f] [AlgebraicStack.FiniteType f]
    (V : AlgebraicSpace.OpenSubspace Y) [AlgebraicSpace.IsQuasiCompact V.X]
    [AlgebraicStack.Gerbe (pullbackSnd f V.ι)] :
    ∃ (Zbar Z : AlgebraicSpace S) (j : Z ⟶ Zbar) (gBar : Zbar ⟶ Y)
      (g : Z ⟶ Y) (h : Z.toGroupoids ⟶ X),
      AlgebraicSpace.IsOpenImmersion j ∧ AlgebraicSpace.Proper gBar ∧
        AlgebraicStack.Proper h ∧ j ≫ gBar = g ∧
          Nonempty (h ≫ f ≅ AlgebraicSpace.toGroupoids.map g) ∧
            V.pointsSet ⊆ Set.range (AlgebraicSpace.Points.map g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
