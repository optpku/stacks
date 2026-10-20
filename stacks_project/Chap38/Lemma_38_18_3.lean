/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Modules.IsPureAlong

/- Lemma 38.18.3: a finite type quasicoherent module that is flat at every point
of the fibre over `s` and pure along that fibre is universally pure along it. -/
@[stacks 05L5] #check
  (AlgebraicGeometry.Scheme.Modules.IsPureAlong.universally_of_flatOverAt :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FiniteType f]
      (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      (s : S) (_ : F.IsPureAlong f s)
      (_ : ∀ x : f.fiber s, flatOverAt F f (f.fiberι s x)),
      F.IsUniversallyPureAlong f s)

end Scheme.Modules.IsPureAlong
end AlgebraicGeometry
