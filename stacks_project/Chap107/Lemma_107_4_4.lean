module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FormalBranches.Multiplicity

import StacksCheckRecall

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
open scoped Bicategory

universe u

/- Lemma 107.4.4: Let `X` be an algebraic stack locally of finite type over a
locally Noetherian scheme `S`. Let `x0` be a finite-type field-valued point of
`X` with image `s ∈ S`. If `S.presheaf.stalk s` is a G-ring, then the map
`toComponent` of Lemma 107.4.2 preserves multiplicities: the multiplicity of a
formal branch equals the multiplicity of its image irreducible component of
`|X|`. -/
@[stacks 0DRD] #check (AlgebraicGeometry.AlgebraicStack.FormalBranches.toComponent_multiplicity :
  ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicGeometry.AlgebraicStack.IsLocallyOfFiniteType X]
    [AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian X]
    (x0 : AlgebraicGeometry.AlgebraicStack.FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (s : S) (hs : x0.structureHom (closedPoint x0.K) = s)
    [IsGRing (S.presheaf.stalk s)]
    {τ : TopologicalSpace (AlgebraicGeometry.AlgebraicStack.Points X)}
    (hτ : AlgebraicGeometry.AlgebraicStack.IsPointsTopology X τ)
    (ξ : GroupoidsOver.FormalObject X)
    [GroupoidsOver.FormalObject.IsVersal ξ]
    (hξ : AlgebraicGeometry.AlgebraicStack.StageOneMarking x0 ξ)
    (Z : irreducibleComponents (PrimeSpectrum ξ.base.carrier)),
    Scheme.irreducibleComponentMultiplicity (Spec (CommRingCat.of ξ.base.carrier)) Z =
      AlgebraicGeometry.AlgebraicStack.irreducibleComponentMultiplicity X τ
        (AlgebraicGeometry.AlgebraicStack.FormalBranches.toComponent x0 hτ
          (AlgebraicGeometry.AlgebraicStack.FormalBranches.mk x0 ξ hξ Z)))
