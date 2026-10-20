/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.GenericFlatness.Stratification

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.54.1 (Generic flatness stratification) -/
@[stacks 0ASY] #check
  (AlgebraicGeometry.Scheme.Modules.exists_genericFlatnessStratification :
    {X S : Scheme.{u}} → (f : X ⟶ S) →
    [CompactSpace X] → [QuasiSeparatedSpace X] →
    [CompactSpace S] → [QuasiSeparatedSpace S] →
    [Scheme.Hom.FinitePresentation f] →
    (F : X.Modules) → [F.IsFinitePresentation] →
    ∃ (t : ℕ) (Z : Fin (t + 1) → S.IdealSheafData)
      (h_finiteType : ∀ i : Fin (t + 1), (Z i).IsFiniteType)
      (h_thickening : IsThickening (Z 0).subschemeι)
      (h_chain : ∀ i : Fin t, Z i.castSucc ≤ Z i.succ)
      (h_last : Z (Fin.last t) = ⊤),
      ∀ i : Fin t,
        Scheme.Modules.flatOver
          ((Scheme.Modules.pullback
            (pullback.fst f (Scheme.Modules.stratumMap Z i))).obj F)
          (pullback.snd f (Scheme.Modules.stratumMap Z i)))
