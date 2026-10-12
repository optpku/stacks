/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flat closed subschemes

Flat closed subschemes are classified by their closed supports that are stable under
generalization, and morphisms whose ranges lie in such supports factor through them.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The support of a flat closed subscheme is stable under generalization. -/
theorem support_stableUnderGeneralization_of_flat
    {X : Scheme.{u}} (I : X.IdealSheafData) (hI : Flat I.subschemeι) :
    StableUnderGeneralization (I.support : Set X) := sorry

/-- The function sending a flat closed subscheme to its support, regarded as a closed subset
stable under generalization. -/
def flatSupport (X : Scheme.{u}) :
    { I : X.IdealSheafData // Flat I.subschemeι } →
      { Z : TopologicalSpace.Closeds X // StableUnderGeneralization (Z : Set X) } :=
  fun I ↦ ⟨I.1.support, support_stableUnderGeneralization_of_flat I.1 I.2⟩

/-- Sending a flat closed subscheme to its support is bijective onto the closed subsets stable
under generalization. -/
theorem flatSupport_bijective (X : Scheme.{u}) :
    Function.Bijective (flatSupport X) := sorry

/-- Two flat ideal-sheaf data on a scheme with the same support are equal. -/
theorem eq_of_flat_of_support_eq {X : Scheme.{u}} (I J : X.IdealSheafData)
    (hI : Flat I.subschemeι) (hJ : Flat J.subschemeι)
    (h_support : (I.support : Set X) = (J.support : Set X)) :
    I = J := sorry

/-- A morphism whose range lies in the support of a flat closed subscheme factors through that
closed subscheme. -/
theorem exists_lift_of_flat_of_range_subset
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (hI : Flat I.subschemeι) (g : Y ⟶ X)
    (hg : Set.range g ⊆ (I.support : Set X)) :
    ∃ g' : Y ⟶ I.subscheme, g' ≫ I.subschemeι = g := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
