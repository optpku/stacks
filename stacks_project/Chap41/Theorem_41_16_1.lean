/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.FormallyEtale
import StacksCheckRecall

open CategoryTheory

universe u

namespace AlgebraicGeometry.Etale

/- Theorem 41.16.1: a locally finitely presented scheme morphism `f : X ⟶ S` is étale
if and only if every commutative square from an affine square-zero closed immersion has a
unique lift. Equivalently, restriction `Mor_S(T', X) → Mor_S(T, X)` is bijective. -/
@[stacks 025K]
#check (AlgebraicGeometry.Etale.iff_existsUnique_lift :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f],
    Etale f ↔
      ∀ {T T' : Scheme.{u}} [IsAffine T] [IsAffine T'] (i : T ⟶ T')
        [IsClosedImmersion i], i.ker ^ 2 = ⊥ →
          ∀ (g : T ⟶ X) (h : T' ⟶ S) (sq : CommSq g i f h),
            Nonempty (Unique sq.LiftStruct))

end AlgebraicGeometry.Etale
