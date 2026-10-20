/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.ShortComplex.IdealPower.Submodule

/-!
# Lemma 15.102.1

@stack 0G3K
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ShortComplex.IdealPower.Submodule

/-
Lemma 15.102.1 (0G3K): let `I` be an ideal of a Noetherian ring `A`, and let
`K ⟶ L ⟶ M` be a complex of finite `A`-modules with homology `H`.  If `H_n` denotes the
homology of `I ^ n K ⟶ I ^ n L ⟶ I ^ n M`, then one positive integer `c` controls all stages:
for `n ≥ c`, the image of `H_n ⟶ H` lies in `I ^ (n - c) H`, and there is a canonical map
`I ^ n H ⟶ H_(n-c)`.  For `n ≥ 2c`, the two composites are the canonical transition maps.
Consequently the inverse systems `(H_n)` and `(I ^ n H)` are isomorphic as pro-objects.

The reusable owners below retain both the literal `n - c` formulation and the more compositional
fixed-shift formulation.  This file is only the source-facing recall boundary.
-/

/- Module-level stages and their functoriality. -/
@[stacks 0G3K "adic submodule stage"]
#check @Ideal.PowerSubmodule.stage
@[stacks 0G3K "adic stage map"]
#check @Ideal.PowerSubmodule.map
@[stacks 0G3K "adic stage map inclusion formula"]
#check @Ideal.PowerSubmodule.map_comp_subtype
@[stacks 0G3K "adic stage functor"]
#check @Ideal.PowerSubmodule.functor

/- Short-complex stages and the two inverse systems. -/
@[stacks 0G3K "adic stage of a short complex"]
#check @stage
@[stacks 0G3K "adic stage homology"]
#check @homologyStage
@[stacks 0G3K "adic stage homology to ambient homology"]
#check @toAmbient
@[stacks 0G3K "adic stage homology tower"]
#check @tower
@[stacks 0G3K "adic homology tower transition formula"]
#check @tower_transitionMap
@[stacks 0G3K "ambient adic homology tower"]
#check @ambientTower
@[stacks 0G3K "ambient adic tower transition formula"]
#check @ambientTower_transitionMap
@[stacks 0G3K "explicit-to-canonical homology comparison"]
#check @ShortComplex.moduleCatHomologyIso

/- Literal source indexing: bounds, canonical factors, and reverse maps. -/
@[stacks 0G3K "canonical reverse comparison specification"]
#check @ReverseSpec
@[stacks 0G3K "canonical adic cycle map to shallower stage cycles"]
#check @cyclesStageToStageCycles
@[stacks 0G3K "canonical reverse comparison specification equivalence"]
#check @reverseSpec_iff
@[stacks 0G3K "adic cycle representative in a shallower stage"]
#check @exists_stageCycle_of_le
@[stacks 0G3K "uniqueness of the canonical reverse comparison"]
#check @reverse_ext
@[stacks 0G3K "eventual image bound for filtered homology"]
#check @ImageBound
@[stacks 0G3K "canonical forward factor for filtered homology"]
#check @forwardMap
@[stacks 0G3K "canonical forward factor inclusion formula"]
#check @forwardMap_comp_subtype
@[stacks 0G3K "shifted factorization image bound"]
#check @Comparison.range_le_of_forwardSpec
@[stacks 0G3K "shifted adic homology comparison"]
#check @Comparison
@[stacks 0G3K "filtered-homology comparison from a finite middle term"]
#check @existsComparison_of_finite_middle
@[stacks 0G3K "shifted filtered-homology comparison from a finite middle term"]
#check @Comparison.existsShiftedComparison_of_finite_middle

/- Fixed-shift maps and the pro-isomorphism API. -/
@[stacks 0G3K "forward shifted filtered-homology map"]
#check @Comparison.Shift
@[stacks 0G3K "reverse shifted filtered-homology map"]
#check @Comparison.ReverseShift
@[stacks 0G3K "two-sided shifted inverse for sequential pro-objects"]
#check @Pro.SequentialHom.IsShiftedInverse
@[stacks 0G3K "shifted filtered-homology comparison predicate"]
#check @Comparison.IsComparison
@[stacks 0G3K "shifted filtered-homology reverse specification"]
#check @Comparison.ReverseShiftSpec
@[stacks 0G3K "canonical shifted filtered-homology forward map"]
#check @Comparison.forwardShift
@[stacks 0G3K "canonical shifted filtered-homology reverse map"]
#check @Comparison.reverseShift
@[stacks 0G3K "indexed comparison to shifted comparison"]
#check @Comparison.isComparison
@[stacks 0G3K "filtered-homology pro-morphism"]
#check @Comparison.proMap
@[stacks 0G3K "reverse filtered-homology pro-morphism"]
#check @Comparison.proReverseMap
@[stacks 0G3K "shifted filtered-homology pro-isomorphism"]
#check @Pro.SequentialHom.IsShiftedInverse.iso

/- Main source statement, checked with all source hypotheses and explicit comparison data. -/
section SourceStatement

universe u v

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A)
variable [Module.Finite A (S.X₁ : Type v)] [Module.Finite A (S.X₂ : Type v)]
variable [Module.Finite A (S.X₃ : Type v)]

@[stacks 0G3K "Lemma 15.102.1 shifted comparison"]
#check (existsComparison S I :
  ∃ c : ℕ, ∃ _ : Comparison S I c, 0 < c)

@[stacks 0G3K "Lemma 15.102.1 shifted comparison data"]
#check (Comparison.existsShiftedComparison S I :
  ∃ c : ℕ, 0 < c ∧ ∃ α : Comparison.Shift S I c,
    ∃ β : Comparison.ReverseShift S I c, Comparison.IsComparison S I c α β)

variable {c n : ℕ} (D : Comparison S I c) (hn : c ≤ n)

@[stacks 0G3K "Lemma 15.102.1 image bound"]
#check (D.imageBound n hn : ImageBound S I c n)

@[stacks 0G3K "Lemma 15.102.1 canonical forward map"]
#check (forwardMap S I c n (D.imageBound n hn) : ForwardMap S I c n)

@[stacks 0G3K "Lemma 15.102.1 canonical reverse map"]
#check (D.reverse n hn : ReverseMap S I c n)

@[stacks 0G3K "Lemma 15.102.1 reverse naturality"]
#check D.reverse_naturality

@[stacks 0G3K "Lemma 15.102.1 canonical reverse specification"]
#check D.reverse_spec n hn

@[stacks 0G3K "Lemma 15.102.1 shifted reverse specification"]
#check D.reverseShift_spec

@[stacks 0G3K "Lemma 15.102.1 canonical shifted maps"]
#check (D.isComparison :
  Comparison.IsComparison S I c D.forwardShift D.reverseShift)

@[stacks 0G3K "Lemma 15.102.1 pro-isomorphism"]
#check D.isComparison.1.isIso

@[stacks 0G3K "Lemma 15.102.1 pro-isomorphism data"]
#check D.toProIso

variable (h : 2 * c ≤ n)

@[stacks 0G3K "Lemma 15.102.1 ambient composite"]
#check D.reverse_forward n h

@[stacks 0G3K "Lemma 15.102.1 homology composite"]
#check D.forward_reverse n h

end SourceStatement
