module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Homology bounds on the small étale derived category

Finite cohomological support is equivalent to the corresponding pair of bounds
for the canonical t-structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open DerivedCategory DerivedCategory.TStructure

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X : Scheme.{u}} {Λ : Type u} [CommRing Λ]
variable [HasSheafify (smallEtaleTopology X) (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify ((smallEtaleTopology X).over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ))]

/-- Homology vanishes outside a finite interval exactly when the canonical
t-structure has the corresponding lower and upper bounds. -/
theorem isZero_homology_iff
    (E : DerivedCategory (Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)))
    (a b : ℤ) :
    IsGE E a ∧ IsLE E b ↔
      ∀ i : ℤ, ¬ (a ≤ i ∧ i ≤ b) →
        IsZero
          ((homologyFunctor
              (Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)) i).obj E) :=
  sorry

end AlgebraicGeometry.Scheme.Etale
