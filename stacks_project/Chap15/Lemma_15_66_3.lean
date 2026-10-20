/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Ext.TensorComparison
import StacksCheckRecall

/-!
@stack 087Q

Lemma 15.66.3 is recalled from the canonical Hom and Ext tensor-comparison maps and their
invertibility criteria.
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 15.66.3 (1) (087Q): the Hom tensor comparison is an isomorphism for a finitely presented
source and a flat tensor factor. -/
@[stacks 087Q "Lemma 15.66.3 (1)"]
#check fun {R : Type u} [CommRing R]
    (M N L : ModuleCat.{u} R) [Module.FinitePresentation R M] [Module.Flat R L] ↦
  (ModuleCat.Ext.TensorComparison.homComparison_isIso_of_finitePresentation M N L :
    IsIso (ModuleCat.Ext.TensorComparison.homComparison M N L))

/- Lemma 15.66.3 (2) (087Q): the degree-`i` Ext tensor comparison is an isomorphism for
`i < m` when the source is `(-m)`-pseudo-coherent and the tensor factor is flat. -/
@[stacks 087Q "Lemma 15.66.3 (2)"]
#check fun {R : Type u} [CommRing R]
    (M N L : ModuleCat.{u} R) (m i : ℕ) [Module.Flat R L]
    (hM : M.IsMPseudoCoherent (-(m : ℤ))) (hi : i < m) ↦
  (ModuleCat.Ext.TensorComparison.extComparison_isIso_of_isMPseudoCoherent
      M N L m i hM hi :
    IsIso (ModuleCat.Ext.TensorComparison.extComparison M N L i))

/- The two concrete comparison morphisms are reusable data owners. -/
#check @CategoryTheory.ModuleCat.Ext.TensorComparison.homComparison
#check @CategoryTheory.ModuleCat.Ext.TensorComparison.extComparison

/- The linear-map form underlying clause (1). -/
#check @CategoryTheory.ModuleCat.Ext.TensorComparison.rTensorHomToHomRTensor_bijective_of_finitePresentation
