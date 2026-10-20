/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian.OpennessOfVersality

/-! Compatibility check for openness of versality of Type-valued functors. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty

universe u v

#check (AlgebraicGeometry.Scheme.Over.OpennessOfVersality :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (AlgebraicGeometry.Scheme.Over.locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v),
    Prop)
