module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.InjectiveAmplitude.Noetherian

@[expose] public section

/-!
# The residue-field criterion for finite injective dimension

@stack 0AVJ

For a local Noetherian ring, the ideal-quotient family collapses to the canonical residue field.
-/

noncomputable section

universe u

open CategoryTheory
open scoped DerivedExt

namespace CategoryTheory.DerivedCategory.HasFiniteInjectiveDimension

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A bounded-below complex with finite cohomology over a local Noetherian ring has finite
injective dimension exactly when its high derived extensions from the residue field vanish. -/
@[stacks 0AVJ "local residue-field criterion"]
theorem iff_eventually_residueField_ext
    (K : DerivedCategory.Plus (ModuleCat R))
    (hKfinite : ∀ i : ℤ,
      Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K.obj)) :
    HasFiniteInjectiveDimension K.obj ↔
      ∃ b : ℤ, ∀ i : ℤ, b < i →
        Subsingleton
          (Ext⁽i⁾((DerivedCategory.singleFunctor (ModuleCat R) 0).obj
            (ModuleCat.of R (IsLocalRing.ResidueField R)), K.obj)) := sorry

end CategoryTheory.DerivedCategory.HasFiniteInjectiveDimension
