/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_8_1_Mono
public import stacks_project.Chap100.Definition_100_12_3_Dimension
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap107.Definition_107_5_14_PseudoCatenary
public import stacks_project.Chap107.Lemma_107_5_24_Jacobson
public import stacks_project.Chap107.«107_5_19_1_Reduced»

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

noncomputable section

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 107.5.21: a locally of finite type monomorphism `i : T ⟶ X` of
algebraic stacks, with `X` (and thus also `T`) Jacobson, pseudo-catenary, and
locally Noetherian, `T` irreducible of finite dimension `d`, and `X` reduced
of dimension at most `d`, admits a nonempty open substack `V` of `T` such
that the induced monomorphism `V.ι ≫ i` is an open immersion identifying
`V` with an open subset of an irreducible component of `X`. -/
@[stacks 0DS2]
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
    ∃ V : OpenSubstack T,
      Nonempty (Points V.Y) ∧ OpenImmersion (V.ι ≫ i) ∧
        ∃ C : @irreducibleComponents (Points X) τ,
          Set.range (Points.map (V.ι ≫ i)) ⊆ (C : Set (Points X)) :=
  sorry

/-- If an open substack `V` of `T` induces an open immersion into `X` whose
image on points is contained in an irreducible component `C` of `|X|`, then
the induced map factors as an open immersion through the reduced induced
closed substack of `C`. -/
theorem openImmersion_factor_irreducibleComponentSubstack
    {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X]
    [IsJacobson T] [IsJacobson X]
    [IsPseudoCatenary T] [IsPseudoCatenary X]
    [IsIrreducible T] [IsReduced X]
    (i : T ⟶ X) [Groupoids.Hom.Mono i] [LocallyOfFiniteType i]
    {d : ℤ} (hT_dim : dimension T = (d : EInt))
    (hX_dim : dimension X ≤ (d : EInt))
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (V : OpenSubstack T) (h_open : OpenImmersion (V.ι ≫ i))
    {C : @irreducibleComponents (Points X) τ}
    (h_subset : Set.range (Points.map (V.ι ≫ i)) ⊆ (C : Set (Points X))) :
    ∃ j : V.Y ⟶ (irreducibleComponentSubstack hτ C).Y,
      OpenImmersion j ∧
        j ≫ (irreducibleComponentSubstack hτ C).ι = V.ι ≫ i :=
  sorry

end AlgebraicGeometry.AlgebraicStack
