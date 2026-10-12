/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ResidueField.Coproduct
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Factorization through residue-field points

This module records criteria for a morphism from a reduced scheme to factor through the
canonical residue-field morphism of a point.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.ResidueField

/-- A morphism from a reduced scheme whose range is contained in a singleton factors through
the canonical morphism from the spectrum of the residue field at that point. -/
theorem exists_factorization_of_range_subset_singleton
    {X Y : Scheme.{u}} (f : Y ⟶ X) (x : X) [IsReduced Y]
    (himage : Set.range f ⊆ {x}) :
    ∃ g : Y ⟶ Spec (X.residueField x), g ≫ X.fromSpecResidueField x = f := sorry

/-- For a morphism from a reduced scheme, factorization through the residue-field point is
equivalent to having range contained in that point. -/
theorem exists_factorization_iff_range_subset_singleton
    {X Y : Scheme.{u}} (f : Y ⟶ X) (x : X) [IsReduced Y] :
    (∃ g : Y ⟶ Spec (X.residueField x), g ≫ X.fromSpecResidueField x = f) ↔
      Set.range f ⊆ {x} := sorry

/-- A morphism from a reduced scheme to a locally Noetherian scheme factors through the
coproduct of the residue-field spectra over `E` when its range lies in `E` and points of `E`
have no nontrivial specializations among themselves. -/
theorem exists_factorization_pointSpectrumCoproduct_of_range_subset
    {X Y : Scheme.{u}} (f : Y ⟶ X) (E : Set X) [IsLocallyNoetherian X] [IsReduced Y]
    (hspecializes : ∀ ⦃x x' : X⦄, x ∈ E → x' ∈ E → Specializes x x' → x = x')
    (himage : Set.range f ⊆ E) :
    ∃ g : Y ⟶ pointSpectrumCoproduct X E, g ≫ pointSpectrumCoproductTo X E = f := sorry

end AlgebraicGeometry.Scheme.Hom.ResidueField

end
