/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.UniversallyExact
import StacksCheckRecall

@[expose] public section

open CategoryTheory LinearMap

universe u v

variable {R : Type u} [CommRing R]

/- Lemma 46.8.4 (1): if `L ⟶ M ⟶ N` remains exact after tensoring with every
`R`-module, then the inclusion of the range of `M ⟶ N` into `N` is universally injective. -/
@[stacks 0701] #check
  (CategoryTheory.ShortComplex.universallyInjective_rangeSubtype :
    ∀ (S : ShortComplex (ModuleCat.{v} R)),
      (∀ (Q : Type (max u v)) (_ : AddCommGroup Q) (_ : Module R Q),
        range (rTensor Q S.f.hom) = ker (rTensor Q S.g.hom)) →
      UniversallyInjective.{u, v, v, max u v} (range S.g.hom).subtype)

/- Lemma 46.8.4 (2): a complex which remains exact after tensoring with every
`R`-module decomposes degreewise into universally exact short exact sequences
`0 ⟶ cycles i ⟶ C.X i ⟶ cycles (i + 1) ⟶ 0`. -/
@[stacks 0701] #check
  (HomologicalComplex.universallyExact_cyclesShortComplex :
    ∀ (C : CochainComplex (ModuleCat.{v} R) ℤ),
      (∀ (i : ℤ) (Q : Type (max u v)) (_ : AddCommGroup Q) (_ : Module R Q),
        range (rTensor Q (C.sc i).f.hom) =
          ker (rTensor Q (C.sc i).g.hom)) →
      ∀ i, (C.cyclesShortComplex i).UniversallyExact)
