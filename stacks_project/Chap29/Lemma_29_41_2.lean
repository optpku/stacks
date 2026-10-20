/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.41.2: a scheme morphism is universally closed exactly when its restrictions over
every member of some open cover of the target are universally closed. -/
@[stacks 02K7] #check
  (AlgebraicGeometry.IsZariskiLocalAtTarget.iff_exists_openCover
    (P := @AlgebraicGeometry.UniversallyClosed) :
      ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
        AlgebraicGeometry.UniversallyClosed f ↔
          ∃ 𝒰 : S.OpenCover.{u}, ∀ i : 𝒰.I₀,
            AlgebraicGeometry.UniversallyClosed (f ∣_ ((𝒰.f i).opensRange)))
