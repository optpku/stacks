/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.IsolatedSingularities
import StacksCheckRecall

/-! # Curves with isolated singularities -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

universe u

/- Lemma 109.14.1 (1): a family belongs to the open substack of curves with
isolated singularities exactly when every closed subspace structure on its
singular locus is finite over the base. -/
@[stacks 0DZW] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_isolatedSingularities_iff :
    ∀ {S : Scheme.{u}} (P : Obj S),
      isolatedSingularities S P ↔
        ∀ T : ClosedSubspaceStructure (nonsmoothLocusClosed (hom P)),
          IsFinite (T.ι ≫ hom P))

/- Lemma 109.14.1 (2): a proper scheme of dimension at most one over a field
belongs to this open substack exactly when it is smooth except at finitely
many points. -/
@[stacks 0DZW] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_isolatedSingularities_iff_finiteNonsmooth :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (hdim : topologicalKrullDim X.left ≤ 1),
      isolatedSingularities (Spec (CommRingCat.of k))
          (mkOfSchemeOverField X hdim) ↔
        Set.Finite (setOf fun x : X.left ↦ ¬ X.hom.SmoothAt x))

#check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.isolatedSingularities_openOnBase :
    ∀ {S : Scheme.{u}} (P : Obj S),
      ∃ U : OpenSubspace (ofOver (base P)),
        IsLargestIsolatedSingularitiesOpen (hom P) U ∧
          ∀ {Q : Obj S} (φ : Q ⟶ P),
            IsLargestIsolatedSingularitiesOpen (hom Q)
                (U.inverseImage (ofOverMap (baseMap φ))) ∧
              (isolatedSingularities S Q ↔
                ∃ χ : ofOver (base Q) ⟶ U.X,
                  χ ≫ U.ι = ofOverMap (baseMap φ)))

#check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsFiberedInGroupoids_isolatedSingularities :
    ∀ S : Scheme.{u},
      Functor.IsFibered.InGroupoids ((isolatedSingularities S).ι ⋙ p S))

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
