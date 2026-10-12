/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.MotivicRealization

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace WeilCohomology.MotivicRealization

/- Compatibility bridge for the motivic-realization classical core. -/
#check (WeilCohomology.MotivicRealization.existsClassicalCore :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      {F : Type v} [Field F] [CharZero F]
      (G : ChowMotive k
        (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k) ⥤
          GradedObject ℤ (ModuleCat F))
      [G.Linear ℚ] [G.Monoidal],
      IsKoszulBraided G →
        (∀ i : ℤ, i ≠ -2 →
          IsZero ((G.obj (ChowMotive.tateTwist (SchemeOverField.point k) 1)) i)) →
        Nonempty (ClassicalCore G))

end WeilCohomology.MotivicRealization
