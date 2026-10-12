/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap41.Definition_41_11_4
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 41.11.5: for a locally finite-type morphism to a locally Noetherian scheme,
the affine-neighborhood and local-ring notions of being étale at a point agree. -/
@[stacks 039N] #check
  (AlgebraicGeometry.Scheme.Hom.etaleAt_iff_stalkMap :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.LocallyOfFiniteType f]
      (x : X), f.EtaleAt x ↔ (f.stalkMap x).hom.EssEtale)
