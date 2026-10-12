/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry

/-- A morphism `f : X ⟶ S` has a quasi-section if some finite surjective `π : S' ⟶ S`
makes the base change `pullback.snd f π` a split epimorphism. -/
def HasQuasiSection {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (S' : Scheme.{u}) (π : S' ⟶ S),
    IsFinite π ∧ Surjective π ∧ IsSplitEpi (pullback.snd f π)

/-- Having a quasi-section is equivalent to the existence of a finite surjective cover
together with an explicit section of the base change. -/
theorem hasQuasiSection_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    HasQuasiSection f ↔
      ∃ (S' : Scheme.{u}) (π : S' ⟶ S) (σ : S' ⟶ pullback f π),
        IsFinite π ∧ Surjective π ∧ σ ≫ pullback.snd f π = 𝟙 S' := sorry

/-- A morphism over `S` from a finite surjective cover yields a quasi-section. -/
theorem HasQuasiSection.of_over {X S S' : Scheme.{u}} {f : X ⟶ S}
    (π : S' ⟶ S) (σ : S' ⟶ X) (h : σ ≫ f = π) [IsFinite π] [Surjective π] :
    HasQuasiSection f := sorry

end AlgebraicGeometry
