module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.InjectiveAmplitude
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

open CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Derived quasicoherent complexes having finite injective dimension on the members of some
affine open cover. -/
def affineLocallyFiniteInjectiveDimension {X : Scheme.{u}} :
    ObjectProperty (DerivedQCoh X) :=
  fun K ↦ ∃ (ι : Type u) (U : ι → X.affineOpens),
    (⨆ i, (U i : X.Opens)) = ⊤ ∧
      ∀ i, DerivedCategory.HasFiniteInjectiveDimension (affineLocalModel K (U i))

/-- Object-level spelling of affine-local finite injective dimension. -/
abbrev AffineLocallyHasFiniteInjectiveDimension {X : Scheme.{u}}
    (K : DerivedQCoh X) : Prop :=
  affineLocallyFiniteInjectiveDimension K

/-- Affine-local finite injective dimension is equivalent to its defining affine-cover
condition. -/
theorem affineLocallyHasFiniteInjectiveDimension_iff_exists_affineCover
    {X : Scheme.{u}} (K : DerivedQCoh X) :
    AffineLocallyHasFiniteInjectiveDimension K ↔
      ∃ (ι : Type u) (U : ι → X.affineOpens),
        (⨆ i, (U i : X.Opens)) = ⊤ ∧
          ∀ i, DerivedCategory.HasFiniteInjectiveDimension (affineLocalModel K (U i)) := sorry

/-- Affine-local finite injective dimension is invariant under isomorphisms. -/
instance affineLocallyFiniteInjectiveDimension_isClosedUnderIsomorphisms
    {X : Scheme.{u}} :
    ObjectProperty.IsClosedUnderIsomorphisms
      (affineLocallyFiniteInjectiveDimension : ObjectProperty (DerivedQCoh X)) := sorry

/-- On a Noetherian scheme, affine-local finite injective dimension implies boundedness. -/
theorem AffineLocallyHasFiniteInjectiveDimension.bounded
    {X : Scheme.{u}} [IsNoetherian X] {K : DerivedQCoh X}
    (hK : AffineLocallyHasFiniteInjectiveDimension K) :
    (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) K.obj := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
