module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import stacks_project.Chap79.Lemma_79_15_8_Scheme
public import stacks_project.Chap79.Lemma_79_15_7_Existence_of_quasi_splitting

/-!
# Quasi-splitting of a groupoid scheme after separated étale localization

In Situation 79.15.4, if the source and target are additionally flat and
locally of finite presentation, then the identity-section finite part is a
scheme separated and étale over `U`, and the restriction of `R` is
quasi-split over a residue-field-preserving point lying over `u`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

universe u

noncomputable section

namespace AlgebraicGeometry.GroupoidScheme

/-- Lemma 79.15.10: In Situation 79.15.4 assume in addition that `s` and `t`
are flat and locally of finite presentation. Then there exists a scheme `U'`,
a separated étale morphism `U' ⟶ U`, and a point `u'` of `U'` lying over `u`
with `κ(u) = κ(u')` such that the restriction `R' = R|_{U'}` of `R` to `U'`
is quasi-split over `u'`. The space `U'` may be taken to be
`(finitePart (ofScheme G)).U.left`, the map `g` to be `finitePartToU`, and
the point `u'` to arise from `quasiSplittingHom`. -/
@[stacks 04RY]
theorem exists_separatedEtale_isQuasiSplitOver {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left) [IsQuasiSplittingSituation G u]
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left] :
    ∃ (U' : Over S) (g : U' ⟶ G.U) (u' : U'.left),
      AlgebraicGeometry.IsSeparated g.left ∧
        AlgebraicGeometry.Etale g.left ∧ g.left u' = u ∧
          IsIso (g.left.residueFieldMap u') ∧
            GroupoidAlgebraicSpace.IsQuasiSplitOver
              (GroupoidAlgebraicSpace.pullback
                (GroupoidAlgebraicSpace.ofScheme G)
                (objectRestrictionHom G (ofOverMap g)))
              (ofOver.pointsEquiv U' u') :=
  sorry

end AlgebraicGeometry.GroupoidScheme
