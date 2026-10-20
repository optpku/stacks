/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Limits
public import ReasLib.CategoryTheory.Preadditive.CompactObject
public import ReasLib.CategoryTheory.ObjectProperty.Orthogonal.Retract

/-!
# Homological Detection Windows in Derived Categories of DG Algebras

This leaf records finite windows of homological degrees which detect maps out of a derived object.
The definitions are representation-free: targets range over the intrinsic derived category and
homology is computed by the descended homology functors.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule.Derived

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, w} R)

/-- The derived objects whose homology vanishes in every degree belonging to `S`. -/
@[stacks 09RA "homology vanishing on a degree set"]
def homologyVanishesOn (S : Set ℤ) : ObjectProperty (Category.{u, v} A) :=
  fun M ↦ ∀ i ∈ S, IsZero ((homologyFunctor A i).obj M)

/-- Membership in `homologyVanishesOn A S` is degreewise homology vanishing on `S`. -/
@[stacks 09RA "degreewise homology-vanishing criterion"]
theorem homologyVanishesOn_iff (S : Set ℤ) (M : Category.{u, v} A) :
    homologyVanishesOn A S M ↔
      ∀ i ∈ S, IsZero ((homologyFunctor A i).obj M) := sorry

/-- The derived objects whose outgoing maps are detected by target homology in degrees from `S`.
Equivalently, every map from such an object to a target with homology vanishing on `S` is zero. -/
@[stacks 09RA "homology-detected derived objects"]
def detectedByHomologyOn (S : Set ℤ) : ObjectProperty (Category.{u, v} A) :=
  (homologyVanishesOn A S).leftOrthogonal

namespace HomologyDetection

/-- Homology detection in a fixed set of degrees is stable under retracts. -/
@[stacks 09RA "retract stability of homology detection"]
instance isStableUnderRetracts (S : Set ℤ) :
    (detectedByHomologyOn A S).IsStableUnderRetracts := sorry

end HomologyDetection

/-- Derived objects having a finite homology-detection window: maps from them vanish on every
target whose homology vanishes throughout some finite interval. -/
@[stacks 09RA "finite homology-detection window"]
def hasFiniteHomologyWindow : ObjectProperty (Category.{u, v} A) :=
  fun E ↦ ∃ a b : ℤ, a ≤ b ∧ detectedByHomologyOn A (Set.Icc a b) E

/-- The witness formulation of a finite homology-detection window. -/
@[stacks 09RA "finite homology-window witness"]
theorem hasFiniteHomologyWindow_iff (E : Category.{u, v} A) :
    hasFiniteHomologyWindow A E ↔
      ∃ a b : ℤ, a ≤ b ∧ detectedByHomologyOn A (Set.Icc a b) E := sorry

namespace FiniteHomologyWindow

/-- Having a finite homology-detection window is stable under retracts. -/
@[stacks 09RA "retract stability of finite homology windows"]
instance isStableUnderRetracts :
    (hasFiniteHomologyWindow A).IsStableUnderRetracts := sorry

/-- Objects with a finite homology-detection window form a triangulated object property. -/
@[stacks 09RA "triangulated closure of finite homology windows"]
instance isTriangulated :
    (hasFiniteHomologyWindow A).IsTriangulated := sorry

end FiniteHomologyWindow

/-- Membership in `detectedByHomologyOn` evaluates to the expected zero-morphism condition. -/
@[stacks 09RA "homology detection zero-morphism criterion"]
theorem detectedByHomologyOn_iff (S : Set ℤ) (E : Category.{u, v} A) :
    detectedByHomologyOn A S E ↔
      ∀ ⦃M : Category.{u, v} A⦄ (f : E ⟶ M),
        homologyVanishesOn A S M → f = 0 := sorry

/-- A homology-detection window may be consumed directly to prove that a morphism is zero. -/
@[stacks 09RA "homology detection zero-morphism application"]
theorem hom_eq_zero_of_detectedByHomologyOn
    {E M : Category.{u, v} A} {S : Set ℤ}
    (hE : detectedByHomologyOn A S E) (hM : homologyVanishesOn A S M)
    (f : E ⟶ M) : f = 0 := sorry

/-- The intrinsic homology-vanishing predicate specializes to ordinary DG-module homology on a
strict representative. -/
@[stacks 09RA "strict-module homology-vanishing bridge"]
theorem homologyVanishesOn_fromModules_iff
    (S : Set ℤ) (M : DifferentialGradedModule.{u, v} A) :
    homologyVanishesOn A S ((fromModules A).obj M) ↔
      ∀ i ∈ S, IsZero (M.homology i) := sorry

/-- Lemma 22.36.5 (09RA): every compact object in the derived category of a DGA has a finite
homology-detection window. -/
@[stacks 09RA]
theorem hasFiniteHomologyWindow_of_isCompactObject
    (E : Category.{u, v} A) (hE : IsCompactObject E) :
    hasFiniteHomologyWindow A E := sorry

/-- The source-facing DG-module specialization of a finite homology-detection window. -/
@[stacks 09RA "DG-module target formulation of finite homology detection"]
theorem exists_module_homologyWindow_of_isCompactObject
    (E : Category.{u, v} A) (hE : IsCompactObject E) :
    ∃ a b : ℤ, a ≤ b ∧
      ∀ (M : DifferentialGradedModule.{u, v} A),
        (∀ i ∈ Set.Icc a b, IsZero (M.homology i)) →
          ∀ f : E ⟶ (fromModules A).obj M, f = 0 := sorry

#synth (hasFiniteHomologyWindow A).IsStableUnderRetracts
#synth (hasFiniteHomologyWindow A).IsClosedUnderIsomorphisms
#synth (hasFiniteHomologyWindow A).IsTriangulated

section

variable (S : Set ℤ)

#synth (detectedByHomologyOn A S).IsStableUnderRetracts
#synth (detectedByHomologyOn A S).IsClosedUnderIsomorphisms

end

end DifferentialGradedModule.Derived
