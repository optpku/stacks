/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.GenericFiber
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 59.72.2: a quasi-compact, quasi-separated, locally finite type morphism with
finite fiber over a generic point is finite over an open neighborhood of that point. -/
@[stacks 03S1] #check
  (AlgebraicGeometry.Scheme.Hom.exists_isFinite_morphismRestrict_of_finiteFiber_at_genericPoint :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
      [QuasiSeparated f] {η : Y}, η ∈ genericPoints Y →
      ({x : X | f x = η} : Set X).Finite →
      ∃ V : Y.Opens, η ∈ V ∧ IsFinite (f ∣_ V))

end AlgebraicGeometry.Scheme.Hom
