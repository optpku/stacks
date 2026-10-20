/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived completion and pseudo-coherent tensor factors

Over a Noetherian ring, derived completion of a bounded-above complex commutes with derived
tensoring by a pseudo-coherent complex.  The finite-module case is exposed through the canonical
degree-zero embedding.

@stack 0EEV
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DerivedTensorProduct

universe u

-- Local instance justification (search instability): expose the standard derived localization
-- only while constructing the module-derived tensor comparison in this file.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModuleCat

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- A finite module over a Noetherian ring is pseudo-coherent when placed in degree zero. -/
@[stacks 0EEV "finite module as a pseudo-coherent derived object"]
theorem isPseudoCoherent_of_finite_of_isNoetherian
    (M : ModuleCat A) (hM : Module.Finite A M) : M.IsPseudoCoherent := sorry
-- Proof strategy: take a finite presentation of `M` over the Noetherian ring and build the
-- standard bounded-above finite-free resolution of its degree-zero derived object.

end CategoryTheory.ModuleCat

namespace DerivedCategory.DerivedCompletion.Tensor

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

-- Local declaration justification (source-local notation): abbreviate the two fixed derived
-- categories used by the completion/tensor comparisons.
local notation "DMod" => DerivedCategory (ModuleCat A)
-- Local declaration justification (source-local notation): distinguish the bounded-above source
-- category from `DMod` without introducing a public notation token.
local notation "DModMinus" => DerivedCategory.Minus (ModuleCat A)

/-- Tensoring the derived completion of a bounded-above complex by a pseudo-coherent complex
produces a derived-complete target. -/
@[stacks 0EEV "derived-complete tensor target"]
theorem target_isDerivedComplete
    (I : Ideal A) (K : DModMinus) (L : DMod) (hL : L.IsPseudoCoherent) :
    (K.obj^∧[I, I.fg_of_isNoetherianRing] ⊗[A]^L L).IsDerivedCompleteWithRespectTo I := sorry
-- Proof strategy: represent `L` by a bounded-above finite-free complex and use closure of
-- derived completeness under finite sums, shifts, cones, and bounded-above limits.

/-- The canonical comparison from the completion of a derived tensor product to the tensor
product of the completed bounded-above factor, obtained from the universal property of derived
completion. -/
@[stacks 0EEV "tensor-completion comparison map"]
noncomputable def comparison
    (I : Ideal A) (K : DModMinus) (L : DMod) (hL : L.IsPseudoCoherent) :
    ((K.obj ⊗[A]^L L)^∧[I, I.fg_of_isNoetherianRing]) ⟶
      (K.obj^∧[I, I.fg_of_isNoetherianRing] ⊗[A]^L L) :=
  DerivedCompletion.lift I I.fg_of_isNoetherianRing
    (target_isDerivedComplete I K L hL)
    ((CategoryTheory.DerivedCategory.DerivedTensor.Right.functor L).map
      (toDerivedCompletion I I.fg_of_isNoetherianRing K.obj))

/-- The tensor-completion comparison is characterized by its composite with the completion unit.
-/
@[stacks 0EEV "tensor-completion comparison unit equation"]
theorem toDerivedCompletion_comp_comparison
    (I : Ideal A) (K : DModMinus) (L : DMod) (hL : L.IsPseudoCoherent) :
    toDerivedCompletion I I.fg_of_isNoetherianRing (K.obj ⊗[A]^L L) ≫
        comparison I K L hL =
      (CategoryTheory.DerivedCategory.DerivedTensor.Right.functor L).map
        (toDerivedCompletion I I.fg_of_isNoetherianRing K.obj) := sorry
-- Proof strategy: unfold `comparison` and apply the universal factorization equation for
-- `DerivedCompletion.lift`.

/-- Lemma 15.95.7 (2): for `K ∈ D^-(A)` and pseudo-coherent `L ∈ D(A)`, the canonical
comparison from the completion of `K ⊗[A]^L L` to `K^∧ ⊗[A]^L L` is an isomorphism. -/
@[stacks 0EEV "(2), completion commutes with pseudo-coherent derived tensor factors"]
theorem comparison_isIso
    (I : Ideal A) (K : DModMinus) (L : DMod) (hL : L.IsPseudoCoherent) :
    IsIso (comparison I K L hL) := sorry
-- Proof strategy: resolve `L` by finite-free terms, prove the comparison for each term, and
-- extend through the bounded-above totalization using exactness of derived completion.

/-- The finite-module specialization of the canonical tensor-completion comparison. -/
@[stacks 0EEV "finite-module tensor-completion comparison"]
noncomputable def moduleComparison
    (I : Ideal A) (K : DModMinus) (M : ModuleCat A) (hM : Module.Finite A M) :
    ((K.obj ⊗[A]^L ModuleCat.single0Functor.obj M)^∧[I, I.fg_of_isNoetherianRing]) ⟶
      (K.obj^∧[I, I.fg_of_isNoetherianRing] ⊗[A]^L ModuleCat.single0Functor.obj M) :=
  comparison I K (ModuleCat.single0Functor.obj M)
    (CategoryTheory.ModuleCat.isPseudoCoherent_of_finite_of_isNoetherian M hM)

/-- The finite-module tensor-completion comparison satisfies the same universal-unit equation. -/
@[stacks 0EEV "finite-module comparison unit equation"]
theorem toDerivedCompletion_comp_moduleComparison
    (I : Ideal A) (K : DModMinus) (M : ModuleCat A) (hM : Module.Finite A M) :
    toDerivedCompletion I I.fg_of_isNoetherianRing
          (K.obj ⊗[A]^L ModuleCat.single0Functor.obj M) ≫
        moduleComparison I K M hM =
      (CategoryTheory.DerivedCategory.DerivedTensor.Right.functor
          (ModuleCat.single0Functor.obj M)).map
        (toDerivedCompletion I I.fg_of_isNoetherianRing K.obj) := sorry
-- Proof strategy: unfold `moduleComparison` and specialize
-- `toDerivedCompletion_comp_comparison` to the degree-zero pseudo-coherent object attached to `M`.

/-- Lemma 15.95.7 (1): for `K ∈ D^-(A)` and a finite `A`-module `M`, the canonical
comparison from the completion of `K ⊗[A]^L M[0]` to `K^∧ ⊗[A]^L M[0]` is an isomorphism. -/
@[stacks 0EEV "(1), completion commutes with finite module tensor factors"]
theorem moduleComparison_isIso
    (I : Ideal A) (K : DModMinus) (M : ModuleCat A) (hM : Module.Finite A M) :
    IsIso (moduleComparison I K M hM) := sorry
-- Proof strategy: apply `comparison_isIso` to `ModuleCat.single0Functor.obj M` using
-- `CategoryTheory.ModuleCat.isPseudoCoherent_of_finite_of_isNoetherian`.

end DerivedCategory.DerivedCompletion.Tensor
