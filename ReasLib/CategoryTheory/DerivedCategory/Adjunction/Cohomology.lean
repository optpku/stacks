/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.IsomorphismProperty
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Devissage
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohomological detection for adjunctions on derived categories

For a triangulated left adjoint, the unit- and counit-isomorphism properties are retract-stable
triangulated object properties.  The bounded devissage API therefore detects either property on
the degree-zero singles of cohomology objects.
-/

open ComplexShape

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.Adjunction

variable {A : Type uA} {B : Type uB}
variable [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable {F : DerivedCategory B ⥤ DerivedCategory A}
variable {G : DerivedCategory A ⥤ DerivedCategory B}
variable (adj : F ⊣ G)

/-- On a two-sided bounded derived object, invertibility of the adjunction unit is detected on
degree-zero singles of cohomology objects. -/
@[stacks 0FX7 "bounded detection of an adjunction unit"]
theorem unitIso_of_bounded_of_homology
    [F.CommShift ℤ] [F.IsTriangulated] (K : DerivedCategory B)
    (hbounded : ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b)
    (hH : ∀ q : ℤ,
      adj.unitIsoProperty
        ((DerivedCategory.singleFunctor B (0 : ℤ)).obj
          ((DerivedCategory.homologyFunctor B q).obj K))) :
    adj.unitIsoProperty K := sorry

/-- On a two-sided bounded derived object, invertibility of the adjunction counit is detected on
degree-zero singles of cohomology objects. -/
@[stacks 0FX7 "bounded detection of an adjunction counit"]
theorem counitIso_of_bounded_of_homology
    [F.CommShift ℤ] [F.IsTriangulated] (K : DerivedCategory A)
    (hbounded : ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b)
    (hH : ∀ q : ℤ,
      adj.counitIsoProperty
        ((DerivedCategory.singleFunctor A (0 : ℤ)).obj
          ((DerivedCategory.homologyFunctor A q).obj K))) :
    adj.counitIsoProperty K := sorry

end CategoryTheory.Adjunction
