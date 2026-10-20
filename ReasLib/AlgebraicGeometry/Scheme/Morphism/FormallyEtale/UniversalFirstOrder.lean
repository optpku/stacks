/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Differentials
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.FormallyUnramified

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormallyEtale

/-- Formal étaleness is equivalent to formal unramifiedness together with
triviality of a universal first-order thickening, to formal unramifiedness together
with vanishing conormal sheaf, and to simultaneous vanishing of relative differentials
and the conormal sheaf. -/
theorem tfae_universalFirstOrder {X S : Scheme.{u}} (f : X ⟶ S)
    (T : Thickening.Over S) (hleft : T.left = Over.mk f)
    [Thickening.IsUniversalFirstOrder T] :
    let i := (Over.forget S).map T.hom
    let C := Scheme.Hom.conormalSheaf i
    List.TFAE [
      FormallyEtale f,
      FormallyUnramified f ∧ IsIso i,
      FormallyUnramified f ∧ Limits.IsZero C,
      Limits.IsZero Ω[f.toShHom] ∧ Limits.IsZero C] := sorry

end AlgebraicGeometry.FormallyEtale
