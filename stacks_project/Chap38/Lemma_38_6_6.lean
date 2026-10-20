/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Devissage.CompleteAt.Existence
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 38.6.6: a finite module over a finite-type ring map acquires a complete
dévissage at the lifted prime after a suitable elementary étale localization. -/
@[stacks 05I1] #check
  (ModuleCat.exists_completeDevissageAt_after_elementaryEtaleLocalization :
    ∀ {R S : Type u} [CommRing R] [CommRing S]
      (f : R →+* S) (hf : f.FiniteType)
      (N : ModuleCat.{u} S) [Module.Finite S N] (q : PrimeSpectrum S),
      let p : PrimeSpectrum R := PrimeSpectrum.comap f q
      ∃ L : RingHom.ElementaryEtaleLocalization.{u, u, u, u} f p q rfl,
        let Sfg : FGAlgCat.{u} L.R' :=
          ⟨@CommAlgCat.of L.R' _ L.S' _ L.right.toAlgebra,
            L.right_finiteType hf⟩
        let Nfg : FGModuleCat.{u} S :=
          ⟨N, (ModuleCat.isFG_iff N).2 inferInstance⟩
        let N' : FGModuleCat.{u} Sfg.obj :=
          (FGModuleCat.extendScalars L.total).obj Nfg
        Nonempty
          (Module.Devissage.CompleteAt L.R' Sfg N' L.p' L.q' L.right_comap))
