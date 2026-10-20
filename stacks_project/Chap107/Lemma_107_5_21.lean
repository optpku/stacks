module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.IrreducibleComponent.OpenImmersion
import StacksCheckRecall

/-!
# Finite-type monomorphisms of matching dimension

A locally of finite type monomorphism of Jacobson, pseudo-catenary, locally
Noetherian algebraic stacks, from an irreducible source of finite dimension `d`
into a reduced target of dimension at most `d`, is an open immersion onto an
open of an irreducible component after shrinking the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Groupoids.Hom (OpenImmersion)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.5.21: a locally of finite type monomorphism of matching finite
dimension restricts to an open immersion from a nonempty open substack onto
an open subset of an irreducible component of the reduced target. -/
@[stacks 0DS2] #check
  (AlgebraicGeometry.AlgebraicStack.exists_openSubstack_openImmersion_subset_irreducibleComponent :
    ∀ {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X]
    [IsJacobson T] [IsJacobson X]
    [IsPseudoCatenary T] [IsPseudoCatenary X]
    [IsIrreducible T] [IsReduced X]
    (i : T ⟶ X) [Groupoids.Hom.Mono i] [LocallyOfFiniteType i]
    {d : ℤ} (hT_dim : dimension T = (d : EInt))
    (hX_dim : dimension X ≤ (d : EInt))
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ),
    ∃ (V : GroupoidsOver S) (hV : AlgebraicStack V) (j : V ⟶ T),
      Nonempty (Points V) ∧ OpenImmersion j ∧ OpenImmersion (j ≫ i) ∧
        ∃ C : @irreducibleComponents (Points X) τ,
          Set.range (Points.map (j ≫ i)) ⊆ (C : Set (Points X)))

-- The open immersion also factors through the reduced induced component.
#check
  (AlgebraicGeometry.AlgebraicStack.openImmersion_factor_irreducibleComponentSubstack :
    ∀ {S : Scheme.{u}} {Y X : GroupoidsOver S}
    [AlgebraicStack Y] [AlgebraicStack X] [IsReduced X]
    (f : Y ⟶ X) (h_open : OpenImmersion f)
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    {C : @irreducibleComponents (Points X) τ}
    (h_subset : Set.range (Points.map f) ⊆ (C : Set (Points X))),
    ∃ j : Y ⟶ (irreducibleComponentSubstack hτ C).Y,
      OpenImmersion j ∧ j ≫ (irreducibleComponentSubstack hτ C).ι = f)

end AlgebraicGeometry.AlgebraicStack
