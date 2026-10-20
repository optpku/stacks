/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay.Locus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay.Slicing

/-!
# Locally quasi-finite factorizations of flat morphisms

This module records the existence of locally quasi-finite flat factorizations
through points in the image of a flat, locally finitely presented morphism.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Flat

/-- A flat, locally finitely presented morphism can be factored over any point
in its image through a morphism whose composite is locally quasi-finite. -/
@[stacks 0571]
theorem exists_locallyQuasiFinite_factorization
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (s : S) (hs : s ∈ Set.range f) :
    ∃ (S' : Scheme.{u}) (h : S' ⟶ X),
      ∃ _ : Flat (h ≫ f),
        ∃ _ : LocallyOfFinitePresentation (h ≫ f),
          ∃ _ : LocallyQuasiFinite (h ≫ f),
            s ∈ Set.range (h ≫ f) := sorry

end AlgebraicGeometry.Flat
