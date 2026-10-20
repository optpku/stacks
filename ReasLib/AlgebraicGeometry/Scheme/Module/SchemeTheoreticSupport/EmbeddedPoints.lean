/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.EmbeddedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Annihilator
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport.Annihilator
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport.Coherent
import ReasLib.RingTheory.Ideal.AssociatedPrime.Embedded

/-!
# Embedded points of scheme-theoretic supports

A coherent module without embedded associated points descends to its scheme-theoretic support,
which has no embedded points.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The scheme-theoretic support of a coherent module without embedded associated points has no
embedded points. -/
theorem embeddedPoints_schemeTheoreticSupport_subscheme_eq_empty
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hℱ : ℱ.embeddedAssociatedPoints = (∅ : Set X)) :
    (schemeTheoreticSupport ℱ).subscheme.embeddedPoints =
      (∅ : Set (schemeTheoreticSupport ℱ).subscheme) := sorry

/-- A coherent module without embedded associated points descends to a coherent module of full
support and without embedded associated points on its scheme-theoretic support. -/
theorem exists_coherent_module_on_schemeTheoreticSupport
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hℱ : ℱ.embeddedAssociatedPoints = (∅ : Set X)) :
    ∃ 𝒢 : (schemeTheoreticSupport ℱ).subscheme.Modules,
      ∃ _ : 𝒢.IsCoherent,
        Nonempty
            ((Scheme.Modules.pushforward (schemeTheoreticSupport ℱ).subschemeι).obj 𝒢 ≅ ℱ) ∧
          𝒢.embeddedAssociatedPoints =
            (∅ : Set (schemeTheoreticSupport ℱ).subscheme) ∧
          RingedSpace.moduleSupport 𝒢 =
            (Set.univ : Set (schemeTheoreticSupport ℱ).subscheme) := sorry

end AlgebraicGeometry.Scheme.Modules
