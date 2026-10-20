/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.ProperHenselian
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 59.91.1: for a proper morphism over a henselian pair, restriction of any sheaf to the
special-fibre pullback induces a bijection on global sections. -/
@[stacks 0A0B] #check
  (AlgebraicGeometry.Scheme.Hom.globalSectionsBijectiveOfProperHenselianPair :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
      (F : X.toTopCat.Sheaf (Type u)),
      Function.Bijective
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
          (pullback.fst f
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).base).unit.app F).hom.app
              (op (⊤ : TopologicalSpace.Opens X.toTopCat))))
