/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.GenericFlatness.Stratification

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FinitePresentation

/-- A finite-presentation morphism between quasi-compact, quasi-separated schemes admits a finite
descending chain of finite-type closed subschemes, beginning with a thickening and ending in the
empty subscheme, over whose successive locally closed strata the morphism is flat. -/
theorem exists_flatStratification
    {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace S] [QuasiSeparatedSpace S]
    [Scheme.Hom.FinitePresentation f] :
    ∃ (t : ℕ) (Z : Fin (t + 1) → S.IdealSheafData)
      (_ : ∀ i : Fin (t + 1), (Z i).IsFiniteType)
      (_ : IsThickening (Z 0).subschemeι)
      (_ : ∀ i : Fin t, Z i.castSucc ≤ Z i.succ)
      (_ : Z (Fin.last t) = ⊤),
      ∀ i : Fin t,
        Flat (pullback.snd f (Scheme.Modules.stratumMap Z i)) := sorry

end AlgebraicGeometry.Scheme.Hom.FinitePresentation
