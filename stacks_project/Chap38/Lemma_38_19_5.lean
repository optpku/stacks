/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.MittagLeffler.Henselian
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

/- Lemma 38.19.5 (1): a finite module over an essentially finite-type local algebra,
flat over a henselian local base, has a directed colimit presentation by free modules whose
transition maps remain injective modulo the maximal ideal of the base. -/
@[stacks 05U7] #check
  (Module.Flat.exists_freePresentation_of_henselian :
    ∀ {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
      [HenselianLocalRing A]
      [IsLocalRing B]
      [IsLocalHom (algebraMap A B)]
      [Algebra.EssFiniteType A B]
      [AddCommGroup N] [Module B N] [Module A N]
      [IsScalarTower A B N] [Module.Finite B N] [Module.Flat A N],
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirectedOrder I)
        (P : ColimitPresentation I (ModuleCat.of A N)),
        (∀ i, Module.Free A (P.diag.obj i)) ∧
          ∀ ⦃i j : I⦄ (hij : i ≤ j),
            Function.Injective
              ((P.diag.map (homOfLE hij)).hom.quotientMapByIdeal (maximalIdeal A)))

/- Lemma 38.19.5 (2): a finite module over an essentially finite-type local algebra,
flat over a henselian local base, is Mittag-Leffler over the base. -/
@[stacks 05U7] #check
  (Module.MittagLeffler.of_henselian_base :
    ∀ {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
      [HenselianLocalRing A]
      [IsLocalRing B]
      [IsLocalHom (algebraMap A B)]
      [Algebra.EssFiniteType A B]
      [AddCommGroup N] [Module B N] [Module A N]
      [IsScalarTower A B N] [Module.Finite B N] [Module.Flat A N],
      Module.MittagLeffler A N)
