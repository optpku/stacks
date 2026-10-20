/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport.PushforwardInvertible
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 56.7.7 -/
@[stacks 0FZQ] #check (AlgebraicGeometry.Scheme.Modules.section_pushforward_iso_of_support_subset :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [f.FiniteType] [IsSeparated f]
    (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent]
    (h_support : Scheme.Modules.moduleSupport F ⊆ Set.range s.base)
    [Scheme.Modules.Invertible ((Scheme.Modules.pushforward f).obj F)] [IsReduced Y],
    Nonempty (F ≅ (Scheme.Modules.pushforward s).obj
      ((Scheme.Modules.pushforward f).obj F)))

end AlgebraicGeometry.Scheme.Modules
