/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Etale

/-- A scheme morphism is étale exactly when it is locally of finite presentation and
formally étale. -/
theorem iff_locallyOfFinitePresentation_and_formallyEtale
    {X S : Scheme.{u}} (f : X ⟶ S) :
    Etale f ↔ LocallyOfFinitePresentation f ∧ FormallyEtale f := sorry

/-- A locally finitely presented scheme morphism is étale exactly when every commutative
square from an affine square-zero closed immersion admits a unique lift. -/
theorem iff_existsUnique_lift {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] :
    Etale f ↔
      ∀ {T T' : Scheme.{u}} [IsAffine T] [IsAffine T'] (i : T ⟶ T')
        [IsClosedImmersion i], i.ker ^ 2 = ⊥ →
          ∀ (g : T ⟶ X) (h : T' ⟶ S) (sq : CommSq g i f h),
            Nonempty (Unique sq.LiftStruct) := sorry

end AlgebraicGeometry.Etale
