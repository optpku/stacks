/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion

/-!
# Slicing Cohen--Macaulay morphisms

This file gives a locally quasi-finite flat slice through a fibrewise closed
point of a Cohen--Macaulay morphism.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.CohenMacaulayAt

/-- A locally finitely presented morphism that is Cohen--Macaulay at a
fibrewise closed point admits a regular immersion through that point whose
composite to the base is flat, locally finitely presented, and locally
quasi-finite, with set-theoretic fibre equal to that point. -/
@[stacks 0570]
theorem exists_regularImmersion_flat_locallyQuasiFinite
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (x : X) (hCM : f.CohenMacaulayAt x)
    (hclosed : f.asFiber x ∈ closedPoints (f.fiber (f x))) :
    ∃ Z : Scheme.{u},
      ∃ i : Z ⟶ X,
        ∃ hxZ : x ∈ Set.range i,
          ∃ hregular : IsRegularImmersion i,
            ∃ hflat : Flat (i ≫ f),
              ∃ hfp : LocallyOfFinitePresentation (i ≫ f),
                ∃ hqf : LocallyQuasiFinite (i ≫ f),
                  Set.range ((i ≫ f).fiberι (f x) ≫ i) = {x} := sorry

end AlgebraicGeometry.Scheme.Hom.CohenMacaulayAt
