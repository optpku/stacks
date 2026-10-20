module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.PseudoCatenary
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Jacobson
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Irreducible
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion

/-!
# Monomorphisms of matching dimension

A locally of finite type monomorphism from an irreducible algebraic stack of
finite dimension into a reduced algebraic stack of no larger dimension becomes
an open immersion into an irreducible component after restricting its source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Groupoids.Hom (OpenImmersion)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A locally of finite type monomorphism between Jacobson, pseudo-catenary,
locally Noetherian algebraic stacks, with irreducible source of finite integer
dimension and reduced target of no larger dimension, restricts to an open
immersion from a nonempty open substack whose image lies in an irreducible
component of the target. -/
theorem exists_openSubstack_openImmersion_subset_irreducibleComponent
    {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X]
    [IsJacobson T] [IsJacobson X]
    [IsPseudoCatenary T] [IsPseudoCatenary X]
    [IsIrreducible T] [IsReduced X]
    (i : T ⟶ X) [Groupoids.Hom.Mono i] [LocallyOfFiniteType i]
    {d : ℤ} (hT_dim : dimension T = (d : EInt))
    (hX_dim : dimension X ≤ (d : EInt))
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ) :
    ∃ (V : GroupoidsOver S) (hV : AlgebraicStack V) (j : V ⟶ T),
      Nonempty (Points V) ∧ OpenImmersion j ∧ OpenImmersion (j ≫ i) ∧
        ∃ C : @irreducibleComponents (Points X) τ,
          Set.range (Points.map (j ≫ i)) ⊆ (C : Set (Points X)) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
