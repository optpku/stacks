module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Subterminal

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

/- Lemma 66.20.1
A subsheaf of the terminal object of the spaces-étale topos is represented by a unique open
subspace, with uniqueness as an open subset of the canonical point space.
-/
@[stacks 04K8] #check (AlgebraicGeometry.AlgebraicSpace.existsUnique_open_iso_openSubspaceSheaf :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) (hF : IsSubterminal F),
    ∃ U : OpenSubspace X,
      Nonempty (F ≅ openSubspaceSheaf U) ∧
        ∀ V : OpenSubspace X, Nonempty (F ≅ openSubspaceSheaf V) →
          V.pointsOpens = U.pointsOpens)

#check (AlgebraicGeometry.AlgebraicSpace.nonempty_iso_openSubspaceSheaf_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) (hF : IsSubterminal F)
    (U : OpenSubspace X),
    Nonempty (F ≅ openSubspaceSheaf U) ↔ U.pointsOpens = subterminalOpens F)

end AlgebraicGeometry.AlgebraicSpace
