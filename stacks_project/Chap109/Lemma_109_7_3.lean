/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.DeligneMumford
import StacksCheckRecall

/-! # Curves with finite reduced automorphism groups -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Lemma 109.7.3 (1): the open Deligne–Mumford locus is maximal. -/
@[stacks 0DSW] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.dm_isLargest :
  ∀ {S : Scheme.{u}} (Q : ObjectProperty (Obj S)) [IsOpenDMSubstack Q],
    Q ≤ dm S)

/- Lemma 109.7.3 (2): a family factors through the Deligne–Mumford locus exactly
when its automorphism algebraic space is unramified over the base. -/
@[stacks 0DSW] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.dm_iff :
  ∀ {S : Scheme.{u}} (P : Obj S), dm S P ↔ IsUnramified P)

/- Lemma 109.7.3 (3): for a proper scheme of dimension at most one over a field,
membership in the Deligne–Mumford locus, geometric reducedness and dimension
zero of the automorphism space, and unramifiedness are equivalent. -/
@[stacks 0DSW] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_dm_tfae_scheme :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (hdim : topologicalKrullDim X.left ≤ 1),
      List.TFAE
        [dm (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim),
          (∀ G : AlgebraicSpace (Spec (CommRingCat.of k)),
            IsRepresentedBy (mkOfSchemeOverField X hdim) G →
              GeometricallyReduced G ∧ dimension G = 0),
          IsUnramified (mkOfSchemeOverField X hdim)])

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
