module

public import stacks_project.Chap66.Lemma_66_20_1_Sheaf

/-!
# Subterminal étale sheaves are representable by unique opens

A subsheaf of the terminal object of the étale topos of an algebraic space is the
representable sheaf of a unique open subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.20.1: let `S` be a scheme and let `X` be an algebraic space over `S`. If `F` is
a subsheaf of the terminal object of the étale topos of `X` (the category
`Sheaf (spacesEtaleTopology X) (Type (u + 1))`, see Sites, Example 7.10.2), then there
exists a unique open `W ⊂ X` such that `F` is isomorphic to the representable sheaf `h_W`,
implemented as `openSubspaceSheaf`. Uniqueness is as an open of `|X|`. -/
@[stacks 04K8]
theorem existsUnique_open_iso_openSubspaceSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) (hF : IsSubterminal F) :
    ∃ U : OpenSubspace X,
      Nonempty (F ≅ openSubspaceSheaf U) ∧
        ∀ V : OpenSubspace X, Nonempty (F ≅ openSubspaceSheaf V) →
          V.pointsOpens = U.pointsOpens :=
  sorry

/-- A subterminal sheaf on `X_spaces,étale` is isomorphic to `openSubspaceSheaf U` if and
only if `U` occupies the unique open of `|X|` representing `F`. -/
theorem nonempty_iso_openSubspaceSheaf_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) (hF : IsSubterminal F)
    (U : OpenSubspace X) :
    Nonempty (F ≅ openSubspaceSheaf U) ↔ U.pointsOpens = subterminalOpens F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
