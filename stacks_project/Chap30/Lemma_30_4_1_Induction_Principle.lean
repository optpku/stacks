/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CompactOpenInduction
import StacksCheckRecall

/-!
# Lemma 30.4.1

The compact-open induction principle for quasi-compact, quasi-separated schemes.
-/

@[expose] public section

universe u

/- Lemma 30.4.1 (Induction Principle): an affine-local property of quasi-compact
opens that is preserved by the stated union step holds on every quasi-compact open. -/
@[stacks 08DR] #check
  (@AlgebraicGeometry.Scheme.compactOpen_induction_principle :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (P : X.Opens → Prop)
      (h_affine : ∀ U : X.affineOpens, P U)
      (h_union : ∀ (U : X.Opens), IsCompact (U : Set X) → ∀ V : X.affineOpens,
        P U → P V → P (U ⊓ V) → P (U ⊔ V)),
      ∀ (U : X.Opens), IsCompact (U : Set X) → P U)

#check
  (@AlgebraicGeometry.Scheme.compactOpen_induction_principle_top :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (P : X.Opens → Prop)
      (h_affine : ∀ U : X.affineOpens, P U)
      (h_union : ∀ (U : X.Opens), IsCompact (U : Set X) → ∀ V : X.affineOpens,
        P U → P V → P (U ⊓ V) → P (U ⊔ V)),
      P (⊤ : X.Opens))
