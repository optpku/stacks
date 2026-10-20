/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap45.Lemma_45_14_7_Theory
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v w x y z

open CategoryTheory
open scoped TensorProduct

namespace WeilCohomology

variable {k : Type u} [Field k]
variable {F : Type v} [Field F] [CharZero F]
variable {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
variable {pointCycle : CHgrade point 0} {H Picard : V → Type x}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, AddCommGroup (Picard X)]

/- Lemma 45.14.7 (1): data (D0), (D1), and (D2') satisfying axioms
(A1)–(A7) satisfy axiom (B)(a): exterior product is a Künneth isomorphism
for smooth-projective objects. -/
@[stacks 0FIL] #check (WeilCohomology.kunnethMap_bijective_of_axiomsA1ToA7 :
  ∀ (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
    cyclePullback cyclePushforward pointCycle H Picard) (X Y : V),
    Function.Bijective (T.kunnethMap X Y))

/- Lemma 45.14.7 (2): data (D0), (D1), and (D2') satisfying axioms
(A1)–(A7) satisfy axiom (B)(b): under the Künneth isomorphism, integration on a
product is the tensor product of the two zero-extended integration maps. -/
@[stacks 0FIL] #check (WeilCohomology.integral_eq_tensorProductTrace_of_axiomsA1ToA7 :
  ∀ (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
    cyclePullback cyclePushforward pointCycle H Picard) (X Y : V) {d e : ℕ}
    (hX : T.IsNonemptyEquidimensional X d) (hY : T.IsNonemptyEquidimensional Y e),
    T.integral (T.product_isNonemptyEquidimensional hX hY) =
      tensorProductTrace (T.kunnethMap X Y)
        (kunnethMap_bijective_of_axiomsA1ToA7 T X Y)
        (T.integral hX) (T.integral hY))

/- Lemma 45.14.7 (3): evaluating axiom (B)(b) on an exterior product gives the
product of the two zero-extended integrals. -/
@[stacks 0FIL] #check (WeilCohomology.integral_kunnethMap_tmul_of_axiomsA1ToA7 :
  ∀ (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
    cyclePullback cyclePushforward pointCycle H Picard) (X Y : V) {d e : ℕ}
    (hX : T.IsNonemptyEquidimensional X d) (hY : T.IsNonemptyEquidimensional Y e)
    (a : H X) (b : H Y),
    T.integral (T.product_isNonemptyEquidimensional hX hY)
        (T.kunnethMap X Y (a ⊗ₜ[F] b)) =
      T.integral hX a * T.integral hY b)

end WeilCohomology
