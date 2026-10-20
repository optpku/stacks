/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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

/-- The ideal sheaf of sections whose germs vanish at every point of `Z`: the largest ideal
sheaf contained in the family `U ↦ ⋂_{x ∈ Z ∩ U} ker (Γ(X, U) → 𝒪_{X,x})`. This keeps the
nilpotents along `Z`, unlike the vanishing ideal defining its reduced induced structure. -/
noncomputable def germVanishing {X : Scheme.{u}} (Z : Set X) : X.IdealSheafData :=
  ofIdeals fun U ↦
    ⨅ x : {x : X // x ∈ Z ∧ x ∈ U.1}, RingHom.ker (X.presheaf.germ U.1 x.1 x.2.2).hom

/-- For a closed subset stable under generalization, the germ-vanishing closed subscheme is
flat over the ambient scheme. -/
theorem flat_subschemeι_germVanishing {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X)
    (hZ : StableUnderGeneralization (Z : Set X)) :
    Flat (germVanishing (Z : Set X)).subschemeι := sorry

/-- For a closed subset stable under generalization, the germ-vanishing closed subscheme has
support exactly that subset. -/
theorem support_germVanishing {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X)
    (hZ : StableUnderGeneralization (Z : Set X)) :
    ((germVanishing (Z : Set X)).support : Set X) = Z := sorry

/-- A flat closed subscheme is contained, scheme theoretically, in every morphism whose range
lies in its support. -/
theorem le_ker_of_flat_of_range_subset
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (hI : Flat I.subschemeι) (g : Y ⟶ X)
    (hg : Set.range g ⊆ (I.support : Set X)) :
    I ≤ g.ker := sorry

/-- The factorization of a morphism whose range lies in the support of a flat closed subscheme
through that closed subscheme. -/
noncomputable def flatLift
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (hI : Flat I.subschemeι) (g : Y ⟶ X)
    (hg : Set.range g ⊆ (I.support : Set X)) : Y ⟶ I.subscheme :=
  IsClosedImmersion.lift I.subschemeι g
    (by rw [I.ker_subschemeι]; exact le_ker_of_flat_of_range_subset I hI g hg)

/-- The flat lift followed by the closed-subscheme inclusion is the original morphism. -/
@[reassoc (attr := simp)]
theorem flatLift_subschemeι
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (hI : Flat I.subschemeι) (g : Y ⟶ X)
    (hg : Set.range g ⊆ (I.support : Set X)) :
    I.flatLift hI g hg ≫ I.subschemeι = g :=
  IsClosedImmersion.lift_fac _ _ _

/-- A morphism whose range lies in the support of a flat closed subscheme factors through that
closed subscheme. -/
theorem exists_lift_of_flat_of_range_subset
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (hI : Flat I.subschemeι) (g : Y ⟶ X)
    (hg : Set.range g ⊆ (I.support : Set X)) :
    ∃ g' : Y ⟶ I.subscheme, g' ≫ I.subschemeι = g :=
  ⟨I.flatLift hI g hg, I.flatLift_subschemeι hI g hg⟩

end AlgebraicGeometry.Scheme.IdealSheafData
