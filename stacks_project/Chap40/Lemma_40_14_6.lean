module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.AffineOpen.IntegralDescent
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open TopologicalSpace

universe u

/- Lemma 40.14.6: an integral morphism meeting every orbit descends an invariant affine
neighbourhood from the restricted groupoid to the original groupoid. -/
@[stacks 0ABE] #check
  (AlgebraicGeometry.GroupoidScheme.exists_invariantAffineOpen_of_pullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      {U' : Over S} (g : U' ⟶ G.U) [AlgebraicGeometry.IsIntegralHom G.s.left]
      [AlgebraicGeometry.IsIntegralHom G.t.left] [AlgebraicGeometry.IsIntegralHom g.left],
      (∀ u : G.U.left, ∃ u' : U'.left,
        g.left u' ∈ G.t.left '' (G.s.left ⁻¹' {u})) →
      (u' : U'.left) → (W' : AlgebraicGeometry.Scheme.Opens U'.left) → u' ∈ W' →
      AlgebraicGeometry.IsAffineOpen W' →
      (G.toPreRelation.pullback g).IsOpenInvariant W' →
      ∃ W : AlgebraicGeometry.Scheme.Opens G.U.left,
        g.left u' ∈ W ∧ AlgebraicGeometry.IsAffineOpen W ∧
          G.toPreRelation.IsOpenInvariant W)
