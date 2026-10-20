/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity.Locus
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Modules.IsPureAlong

/- Lemma 38.18.6: for a finitely presented morphism `f : X ⟶ S` and a finitely
presented module `F` on `X` that is flat over `S`, the locus of points `s : S`
where `F` is pure along the fibre over `s` is open. -/
@[stacks 05MC] #check
  (AlgebraicGeometry.Scheme.Modules.IsPureAlong.isOpen :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
      (F : X.Modules) [F.IsFinitePresentation]
      [SheafOfModules.IsFlatOver F f.toShHom],
      IsOpen {s : S | F.IsPureAlong f s})

end Scheme.Modules.IsPureAlong
end AlgebraicGeometry
