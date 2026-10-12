/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import stacks_project.Chap79.Lemma_79_15_5_Existence_of_strong_splitting_ResiduePoint
public import stacks_project.Chap79.Lemma_79_15_8_Scheme
public import stacks_project.Chap79.Situation_79_15_2_Strong_splitting

/-!
# Strong splitting after a separated étale scheme localization

In Situation 79.15.2, if the source and target are also flat and locally of
finite presentation, the finite-part localization of Lemma 79.15.5 may be
taken to be a scheme, separated and étale over `U`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Lemma 79.15.8: in Situation 79.15.2, if `s` and `t` are also flat and
locally of finite presentation, then there exist a scheme `U'` over `S`, a
separated étale morphism `g : U' ⟶ U`, and a point `u'` of `U'` lying over
`u` with `IsIso (g.left.residueFieldMap u')` such that the restriction of `R`
to `U'` is strongly split over `u'`. The space `U'` may be taken to be
`(finitePart (ofScheme G)).U.left`, the map `g` to be `finitePartToU`, and
the point `u'` to arise from `strongSplittingHom`. -/
@[stacks 04RX]
theorem exists_separatedEtale_scheme_isStronglySplitOver {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [StrongSplitting G u]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left] :
    ∃ (U' : Over S) (g : U' ⟶ G.U) (u' : U'.left),
      IsSeparated g.left ∧ AlgebraicGeometry.Etale g.left ∧ g.left u' = u ∧
        IsIso (g.left.residueFieldMap u') ∧
          GroupoidAlgebraicSpace.IsStronglySplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G (ofOverMap g)))
            (ofOver.pointsEquiv U' u') :=
  sorry

/-- There exist a scheme `U'` over `S`, a separated étale morphism `U' ⟶ U`,
and a `Spec(κ(u))`-point of `U'` lying over `u` at which the restriction of
`R` is strongly split. Equality of residue fields is encoded by the domain
`Spec(κ(u))`. -/
theorem exists_separatedEtale_residueMap_isStronglySplitOver {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [StrongSplitting G u]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left] :
    ∃ (U' : Over S) (g : U' ⟶ G.U)
      (u' : ofOver (residueOver G u) ⟶ ofOver U'),
      IsSeparated g.left ∧ AlgebraicGeometry.Etale g.left ∧
        u' ≫ ofOverMap g = residueMap G u ∧
          GroupoidAlgebraicSpace.IsStronglySplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G (ofOverMap g)))
            (residueFieldPoint G u u') :=
  sorry

end AlgebraicGeometry.GroupoidScheme
