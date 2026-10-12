/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Effectivity

/-!
# Local effectivity of scheme descent data

Effectivity of scheme descent data can be checked on invariant open neighborhoods.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DescentData.IsEffective

/-- A descent datum relative to a surjective, quasi-compact, flat morphism is effective
if every point has an effective open subdatum containing it. -/
theorem ofLocally {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f] [QuasiCompact f] [Flat f]
    (D : Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f))
    (h : ∀ v : (D.obj PUnit.unit).left,
      ∃ (E : Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f)) (j : E ⟶ D),
        IsOpenImmersion (j.hom PUnit.unit).left ∧
          v ∈ Set.range (j.hom PUnit.unit).left.base ∧ IsEffective E) :
    IsEffective D := sorry

end AlgebraicGeometry.Scheme.DescentData.IsEffective
