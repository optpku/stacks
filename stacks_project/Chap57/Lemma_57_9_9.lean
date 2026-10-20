/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Boundedness
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
universe u v w

namespace AlgebraicGeometry.Scheme.ModuleDerived

/- Lemma 57.9.9 (1): a homological functor with finite shifted support on every
perfect object has a uniform symmetric bound on all coherent modules. -/
@[stacks 0FZ8] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.exists_shiftVanishingIn_coherent :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [Smooth f]
      {A : Type v} [Category.{w} A] [Abelian A]
      (H : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace) ⥤ A)
      [H.IsHomological] [H.ShiftSequence ℤ],
      (∀ K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace),
        H.shiftVanishingBounded K) →
      ∃ m : ℕ+, ∀ (F : X.Modules) (hF : F.IsCoherent),
        H.shiftVanishingIn (-(m : ℤ)) (m : ℤ) (Perfect.ofCoherent f F hF))

/- Lemma 57.9.9 (2): the cohomological formulation uses the covariant functor
`H.rightOp` as in Derived Categories, Definition 13.3.5. -/
@[stacks 0FZ8] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.exists_shiftVanishingIn_coherent_cohomological :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [Smooth f]
      {A : Type v} [Category.{w} A] [Abelian A]
      (H : (RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))ᵒᵖ ⥤ A)
      [H.rightOp.IsHomological] [H.rightOp.ShiftSequence ℤ],
      (∀ K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace),
        H.rightOp.shiftVanishingBounded K) →
      ∃ m : ℕ+, ∀ (F : X.Modules) (hF : F.IsCoherent),
        H.rightOp.shiftVanishingIn (-(m : ℤ)) (m : ℤ) (Perfect.ofCoherent f F hF))

end AlgebraicGeometry.Scheme.ModuleDerived
