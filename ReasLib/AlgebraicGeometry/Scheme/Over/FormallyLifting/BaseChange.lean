/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyLifting

/-!
# Base change of formal lifting properties

Formal smoothness, formal étaleness, and formal unramifiedness of a
transformation of functors on schemes over a base are stable under fibre-product
base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u v

namespace AlgebraicGeometry.Scheme.Over

namespace FormallySmooth

/-- Formal smoothness of a transformation of functors is stable under base change. -/
instance instIsStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@FormallySmooth S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type v)) := sorry

/-- The base change of a formally smooth transformation of functors is formally smooth. -/
instance pullback_fst {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (b : H ⟶ G) [HasPullback b a] [FormallySmooth a] :
    FormallySmooth (pullback.fst b a) := sorry

end FormallySmooth

namespace FormallyEtale

/-- Formal étaleness of a transformation of functors is stable under base change. -/
instance instIsStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@FormallyEtale S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type v)) := sorry

/-- The base change of a formally étale transformation of functors is formally étale. -/
instance pullback_fst {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (b : H ⟶ G) [HasPullback b a] [FormallyEtale a] :
    FormallyEtale (pullback.fst b a) := sorry

end FormallyEtale

namespace FormallyUnramified

/-- Formal unramifiedness of a transformation of functors is stable under base change. -/
instance instIsStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@FormallyUnramified S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type v)) := sorry

/-- The base change of a formally unramified transformation of functors is formally unramified. -/
instance pullback_fst {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (b : H ⟶ G) [HasPullback b a] [FormallyUnramified a] :
    FormallyUnramified (pullback.fst b a) := sorry

end FormallyUnramified

end AlgebraicGeometry.Scheme.Over
