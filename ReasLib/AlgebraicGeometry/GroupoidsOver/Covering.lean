/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.Groupoids.GerbeMorphism
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!
# Coverings by the essential image of a morphism of groupoid-fibred categories

The covering predicate is the canonical cover-density property of the
underlying functor on the associated site.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/-- A morphism of groupoid-fibred categories covers by essential image when its
underlying functor is cover dense for the associated topology. -/
abbrev coversByEssentialImage (f : U ⟶ X) (τ : StandardTopology) : Prop :=
  (toFunctor f).IsCoverDense (X.associatedTopology τ)

/-- The cover-density predicate is characterized by covering families whose
members are isomorphic to objects in the essential image. -/
theorem coversByEssentialImage_iff (f : U ⟶ X) (τ : StandardTopology) :
    coversByEssentialImage f τ ↔
      ∀ x : X.total,
        ∃ (ι : Type (u + 1)) (Y : ι → X.total) (π : ∀ i, Y i ⟶ x),
          Sieve.generate (Presieve.ofArrows Y π) ∈ X.associatedTopology τ x ∧
            ∀ i, ∃ u : U.total, Nonempty (Y i ≅ (toFunctor f).obj u) :=
  sorry

/-- Cover density on the associated site is equivalent to local essential
surjectivity on the corresponding big site. -/
theorem coversByEssentialImage_iff_locallyEssentiallySurjective
    (f : U ⟶ X) (τ : StandardTopology) :
    coversByEssentialImage f τ ↔
      Hom.LocallyEssentiallySurjective (τ.overTopology S) f :=
  sorry

end AlgebraicGeometry.GroupoidsOver
