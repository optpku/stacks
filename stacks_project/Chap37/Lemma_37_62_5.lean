/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.62.5: for a ring map `f : A ⟶ B`, the induced morphism
`Spec B ⟶ Spec A` is locally of complete-intersection type if and only if `f` is a local
complete-intersection ring homomorphism. -/
@[stacks 07DB] #check
  (AlgebraicGeometry.LocallyOfType.isLocalCompleteIntersection_specMap_iff :
    ∀ {A B : CommRingCat.{u}} (f : A ⟶ B),
      AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection
          (AlgebraicGeometry.Spec.map f) ↔
        f.hom.IsLocalCompleteIntersection)
