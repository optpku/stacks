/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Ext.FlatTensorComparison
import StacksCheckRecall

/-!
# Flat base change for Hom and Ext

Lemma 15.66.4 identifies the canonical Hom and Ext comparison maps after a flat extension of
scalars.  ReasLib owns the explicit maps for an arbitrary ring homomorphism; this file records the
`algebraMap` specialization from the source.

@stack 087R
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 15.66.4 (1): for a flat map `R → R'` and a finitely presented `R`-module `M`,
the canonical map from `R' ⊗[R] Hom_R(M, N)` to the Hom group after scalar extension is an
isomorphism. -/
@[stacks 087R "Lemma 15.66.4 (1)"]
#check fun {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M N : ModuleCat.{u} R) [Module.FinitePresentation R M]
    (hf : (algebraMap R S).Flat) ↦
  (ModuleCat.Ext.FlatTensorComparison.homComparison_isIso_of_finitePresentation M N hf :
    IsIso (ModuleCat.Ext.FlatTensorComparison.homComparison (S := S) M N))

/- Lemma 15.66.4 (2): if `M` is `(-m)`-pseudo-coherent, the canonical Ext comparison is an
isomorphism in every degree `i < m`. -/
@[stacks 087R "Lemma 15.66.4 (2)"]
#check fun {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M N : ModuleCat.{u} R) (m i : ℕ) (hf : (algebraMap R S).Flat)
    (hM : M.IsMPseudoCoherent (-(m : ℤ))) (hi : i < m) ↦
  (ModuleCat.Ext.FlatTensorComparison.extComparison_isIso_of_isMPseudoCoherent
      M N m i hf hM hi :
    IsIso (ModuleCat.Ext.FlatTensorComparison.extComparison M N hf i))

/- Lemma 15.66.4, final assertion: over a Noetherian ring, a finite source module satisfies the Ext
base-change comparison in every degree. -/
@[stacks 087R "Lemma 15.66.4, final assertion"]
#check fun {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    (M N : ModuleCat.{u} R) [Module.Finite R M]
    (hf : (algebraMap R S).Flat) (i : ℕ) ↦
  (ModuleCat.Ext.FlatTensorComparison.extComparison_isIso_of_isNoetherianRing_of_finite
      M N hf i :
    IsIso (ModuleCat.Ext.FlatTensorComparison.extComparison M N hf i))

/- The two concrete base-change comparison morphisms are reusable setup data. -/
#check @ModuleCat.Ext.FlatTensorComparison.homComparison

#check @ModuleCat.Ext.FlatTensorComparison.extComparison
