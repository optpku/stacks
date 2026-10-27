/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.IsomOpenImmersion
import StacksCheckRecall

/-!
# Lemma 108.10.3

With `B`, `Y`, `X` as in the introduction of this section, and assuming in
addition that `X ⟶ B` is proper, the subfunctor of isomorphisms in the
functor of relative morphisms is an open subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite
open AlgebraicGeometry.AlgebraicSpace.RelativeHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Y B X : AlgebraicSpace S}

/- Lemma 108.10.3: with `B`, `Y`, `X` as in the introduction of this section,
in addition assume `X ⟶ B` is proper. Then the subfunctor
`Isom_B(Y, X) ⊂ Mor_B(Y, X)` of isomorphisms is an open subspace. -/
@[stacks 0DPP] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativeHom.isOpenImmersion_isomι :
    ∀ (y : Y ⟶ B) (x : X ⟶ B),
      [Flat y] → [Proper y] → [FinitePresentation y] →
      [FinitePresentation x] → [Proper x] →
      Quot.IsOpenImmersionOnSchemesOver (isomSubfunctor y x).ι)

/- A test morphism factors through an open precisely when the base-changed
relative morphism is invertible. -/
#check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.exists_opens_isIso_iff :
  ∀ (y : Y ⟶ B) (x : X ⟶ B),
    [Flat y] → [Proper y] → [FinitePresentation y] →
    [FinitePresentation x] → [Proper x] →
    ∀ (σ : SchemeOver B) (b : (mor y x).obj (op σ)),
      ∃ U : (σ.left.left).Opens,
        ∀ {τ : SchemeOver B} (h : τ ⟶ σ),
          Nonempty (Over.mk h.left.left ⟶ Over.mk U.ι) ↔
            IsIso (restrict y x h b))

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
