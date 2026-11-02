/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import ReasLib.RingTheory.Gorenstein.CohenMacaulay
public import ReasLib.RingTheory.Gorenstein.InjectiveDimension

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Gorenstein

/-- Every Gorenstein scheme is Cohen-Macaulay. -/
instance instCohenMacaulay (X : Scheme.{u}) [Gorenstein X] : CohenMacaulay X := by
  apply ((cohenMacaulay_tfae_stalk_and_closedPointStalk X).out 0 1).mpr
  refine ⟨inferInstance, fun x ↦ ?_⟩
  letI : IsGorensteinLocalRing (X.presheaf.stalk x) := stalkIsGorenstein x
  letI : IsGorensteinRing (X.presheaf.stalk x) :=
    IsGorensteinRing.of_injectiveDimension_self_ne_top _
      (IsGorensteinLocalRing.finiteSelfInjectiveDimension (R := X.presheaf.stalk x))
  infer_instance

end AlgebraicGeometry.Scheme.Gorenstein
