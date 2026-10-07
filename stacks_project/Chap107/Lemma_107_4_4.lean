module

public import ReasLib.AlgebraicGeometry.Scheme.IrreducibleComponent.Multiplicity
public import ReasLib.RingTheory.Regular.GRing
public import stacks_project.Chap107.Definition_107_3_4_Multiplicity
public import stacks_project.Chap107.Lemma_107_4_2_ComponentsMap

/-!
# Formal branches preserve multiplicities of irreducible components

In the situation of Lemma 107.4.2, if the stalk of `S` at the image of a
finite-type field-valued point is a G-ring, then the canonical map from formal
branches through that point to irreducible components of `|X|` preserves
multiplicities.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.FormalBranches

/-- Lemma 107.4.4: Let `X` be an algebraic stack locally of finite type over a
locally Noetherian scheme `S`. Let `x0` be a finite-type field-valued point of
`X` with image `s ∈ S`. If `S.presheaf.stalk s` is a G-ring, then the map
`toComponent` of Lemma 107.4.2 preserves multiplicities: the multiplicity of a
formal branch equals the multiplicity of its image irreducible component of
`|X|`. -/
@[stacks 0DRD]
theorem toComponent_multiplicity {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyOfFiniteType X]
    [IsLocallyNoetherian X] (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (s : S) (hs : x0.structureHom (closedPoint x0.K) = s)
    [IsGRing (S.presheaf.stalk s)]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (ξ : GroupoidsOver.FormalObject X)
    [GroupoidsOver.FormalObject.IsVersal ξ] (hξ : StageOneCompatible x0 ξ)
    (Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier)) :
    Scheme.irreducibleComponentMultiplicity (Spec (CommRingCat.of ξ.base.carrier)) Z =
      irreducibleComponentMultiplicity X τ (toComponent x0 hτ (mk x0 ξ hξ Z)) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.FormalBranches
