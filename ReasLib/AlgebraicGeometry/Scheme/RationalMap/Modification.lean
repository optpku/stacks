/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Extending partial maps after proper modifications

A partial map from a Noetherian scheme to a proper scheme over a common base extends to a
morphism after replacing its source by a proper morphism that is an isomorphism over the
partial map's domain.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PartialMap

/-- A partial map from a Noetherian scheme to a proper scheme over a common base extends after
a proper replacement of its source that is an isomorphism over the map's domain. -/
theorem exists_properModification
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [IsNoetherian X] [IsProper (Y ↘ S)]
    (f : X.PartialMap Y) [f.IsOver S] :
    ∃ (X' : Scheme.{u}) (p : X' ⟶ X) (f' : X' ⟶ Y),
      IsProper p ∧
        IsIso (p ∣_ f.domain) ∧
          f' ≫ (Y ↘ S) = p ≫ (X ↘ S) ∧
            (p ⁻¹ᵁ f.domain).ι ≫ f' = (p ∣_ f.domain) ≫ f.hom := sorry

end AlgebraicGeometry.Scheme.PartialMap
