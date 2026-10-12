/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import stacks_project.Chap79.Lemma_79_15_6_Existence_of_splitting

/-!
# Existence of a splitting after a separated étale localization by a scheme

In Situation 79.15.3, if the source and target are also flat and locally of
finite presentation, there exist a scheme `U'`, a separated étale morphism
`U' ⟶ U`, and a point `u'` of `U'` lying over `u` with `κ(u) = κ(u')` such
that the restriction of `R` to `U'` is split over `u'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

universe u

noncomputable section

namespace AlgebraicGeometry.GroupoidScheme

/-- Lemma 79.15.9: in Situation 79.15.3, if `s` and `t` are also flat and
locally of finite presentation, then there exists a scheme `U'`, a separated
étale morphism `U' ⟶ U`, and a point `u'` of `U'` lying over `u` with
`κ(u) = κ(u')` such that the restriction `R'` of `R` to `U'` is split over
`u'`. -/
@[stacks 0DTD]
theorem exists_separatedEtale_isSplitOver {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [IsSplittingSituation G u]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left] :
    ∃ (U' : Over S) (g : U' ⟶ G.U) (u' : U'.left),
      AlgebraicGeometry.IsSeparated g.left ∧
        AlgebraicGeometry.Etale g.left ∧ g.left u' = u ∧
          IsIso (g.left.residueFieldMap u') ∧
            GroupoidAlgebraicSpace.IsSplitOver
              (GroupoidAlgebraicSpace.pullback
                (GroupoidAlgebraicSpace.ofScheme G)
                (objectRestrictionHom G (ofOverMap g)))
              (ofOver.pointsEquiv U' u') :=
  sorry

end AlgebraicGeometry.GroupoidScheme
