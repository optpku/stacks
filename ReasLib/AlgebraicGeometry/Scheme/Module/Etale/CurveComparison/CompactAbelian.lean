/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactRepresentationDuality
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat

noncomputable section

universe u

namespace CompactModule

variable (Λ : Type u) [CommRing Λ] [Finite Λ]

/-- Finite products are transported through the specified character equivalence. -/
instance : HasFiniteProducts (CompactModule Λ) := by sorry

instance : ((characterEquivalence Λ).inverse).IsEquivalence :=
  (characterEquivalence Λ).isEquivalence_inverse

/-- The abelian structure is transported along the actual continuous character
equivalence; its preadditive operations remain the pointwise ones above. -/
instance : Abelian (CompactModule Λ) :=
  abelianOfEquivalence (characterEquivalence Λ).inverse

end CompactModule

namespace CompactRepresentation

variable (Λ G : Type u) [CommRing Λ] [Finite Λ]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

instance : Preadditive (Cat Λ G) := inferInstanceAs
  (Preadditive ((continuousAction Λ G).FullSubcategory))

instance : HasFiniteProducts (Cat Λ G) := by sorry

instance : ((equivalence Λ G).inverse).IsEquivalence :=
  (equivalence Λ G).isEquivalence_inverse

instance : Abelian (Cat Λ G) := abelianOfEquivalence (equivalence Λ G).inverse

/-- These projectives are compact duals of ambient injectives, not finite or
all-discrete projective substitutes. -/
theorem dual_projective (M : DiscreteModuleCat Λ G) [Injective M] :
    Projective (dual Λ G M) := by sorry

end CompactRepresentation
