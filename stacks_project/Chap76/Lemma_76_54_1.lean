/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Descent
import StacksCheckRecall

/-!
# Fpqc descent of m-pseudo-coherence on algebraic spaces

An object of `D_QCoh(𝒪_X)` is `m`-pseudo-coherent if and only if each derived
pullback along an fpqc covering of `X` is `m`-pseudo-coherent.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u v

/- Lemma 76.54.1: Let `S` be a scheme. Let `{f_i : X_i ⟶ X}` be an fpqc covering
of algebraic spaces over `S`. Let `E` in `D_QCoh(𝒪_X)`. Let `m` in `ℤ`. Then `E`
is `m`-pseudo-coherent if and only if each `Lf_i^* E` is `m`-pseudo-coherent,
where `Lf_i^*` is `ModuleDerived.pullback (family i).hom`. -/
@[stacks 0DL1] #check
  (AlgebraicGeometry.AlgebraicSpace.isMPseudoCoherent_iff_fpqcCovering :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
      (family : ι → Over X) (hfamily : FpqcCovering family)
      (E : ModuleDerived X) (hE : derivedQuasiCoherentModuleProperty X E) (m : ℤ),
      IsMPseudoCoherent X E m ↔
        ∀ i, IsMPseudoCoherent (family i).left
          ((ModuleDerived.pullback (family i).hom).obj E) m)
