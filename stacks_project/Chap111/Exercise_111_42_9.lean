module

public import ReasLib.RingTheory.SimpleModule.RightDerived
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

/- Exercise 111.42.9 -/
@[stacks 0D8Y] #check
  (CommRing.exists_pi_field_of_leftExact_rightDerived_eq_zero :
    ∀ {R : Type u} [CommRing R],
      (∀ (F : ModuleCat.{u} R ⥤ AddCommGrpCat.{u}) [PreservesFiniteLimits F],
        ∀ n : ℕ, 0 < n → ∀ M : ModuleCat.{u} R,
          IsZero ((F.rightDerived n).obj M)) →
      ∃ (n : ℕ) (K : Fin n → Type u) (_ : ∀ i, Field (K i)),
        Nonempty (R ≃+* ((i : Fin n) → K i)))
