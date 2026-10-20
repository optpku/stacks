/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Effectivity.Local
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DescentData
namespace IsEffective

/- Lemma 35.35.13: a descent datum relative to a surjective, quasi-compact, flat
morphism is effective if every point has an effective invariant open neighborhood. -/
@[stacks 0AP4]
#check (AlgebraicGeometry.Scheme.DescentData.IsEffective.ofLocally :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f] [QuasiCompact f] [Flat f]
    (D : Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f))
    (h : ∀ v : (D.obj PUnit.unit).left,
      ∃ (E : Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f)) (j : E ⟶ D),
        IsOpenImmersion (j.hom PUnit.unit).left ∧
          v ∈ Set.range (j.hom PUnit.unit).left.base ∧ IsEffective E),
    IsEffective D)

end IsEffective
end AlgebraicGeometry.Scheme.DescentData
