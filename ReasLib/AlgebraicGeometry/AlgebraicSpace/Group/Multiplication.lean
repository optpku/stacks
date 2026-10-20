module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen

/-!
# Multiplication of group algebraic spaces over a field

The multiplication morphism of a group algebraic space over a field is flat
and universally open.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- The multiplication morphism of a group algebraic space over a field
spectrum is flat. -/
instance instFlat_mul {S : Scheme.{u}} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S}
    (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ))) :
    AlgebraicSpace.Flat (μ[G.X]).left := sorry

/-- The multiplication morphism of a group algebraic space over a field
spectrum is universally open. -/
instance instUniversallyOpen_mul {S : Scheme.{u}} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S}
    (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ))) :
    AlgebraicSpace.UniversallyOpen (μ[G.X]).left := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
