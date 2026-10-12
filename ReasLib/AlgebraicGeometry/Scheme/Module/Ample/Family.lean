/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample

/-!
# Ample families of invertible scheme modules

This leaf extends the single-module ampleness owner with the indexed-family
condition used for schemes that need several affine charts. The family owner
lives next to `Scheme.Modules.IsAmple`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {ι : Type v}

/-- Every point has an affine nonvanishing neighborhood from a positive tensor power of one
member of an indexed family of invertible scheme modules. -/
def AffineNonvanishingFamily (L : ι → X.Modules) : Prop :=
  ∃ hL : ∀ i : ι, Invertible (L i),
    ∀ x : X, ∃ i : ι, ∃ n : ℕ, 0 < n ∧
      ∃ s : Γ(RingedSpace.TensorPower.sheaf (L i) n, ⊤),
        AffineOpenNeighborhood x ((hL i).nonvanishingOpen s)

/-- An indexed family of invertible scheme modules is ample when the scheme is quasi-compact and
the family supplies affine nonvanishing neighborhoods at every point. -/
def AmpleFamily (L : ι → X.Modules) : Prop :=
  IsCompact (Set.univ : Set X) ∧ AffineNonvanishingFamily L

/-- An affine nonvanishing family consists of pointwise invertibility witnesses together with
an affine nonvanishing neighborhood at every point. -/
theorem affineNonvanishingFamily_iff_exists (L : ι → X.Modules) :
    AffineNonvanishingFamily L ↔
      ∃ hL : ∀ i : ι, Invertible (L i),
        ∀ x : X, ∃ i : ι, ∃ n : ℕ, 0 < n ∧
          ∃ s : Γ(RingedSpace.TensorPower.sheaf (L i) n, ⊤),
            AffineOpenNeighborhood x ((hL i).nonvanishingOpen s) := sorry

/-- Unfolding form of the affine nonvanishing condition for a family. -/
theorem affineNonvanishingFamily_iff
    (L : ι → X.Modules)
    [∀ i : ι, Invertible (L i)] :
    AffineNonvanishingFamily L ↔
      ∀ x : X, ∃ i : ι, ∃ n : ℕ, 0 < n ∧
        ∃ s : Γ(RingedSpace.TensorPower.sheaf (L i) n, ⊤),
          AffineOpenNeighborhood x
            ((inferInstance : Invertible (L i)).nonvanishingOpen s) := sorry

/-- An ample family consists of compatible pointwise invertibility witnesses, quasi-compactness,
and an affine nonvanishing neighborhood at every point. -/
theorem ampleFamily_iff_exists (L : ι → X.Modules) :
    AmpleFamily L ↔
      ∃ hL : ∀ i : ι, Invertible (L i),
        IsCompact (Set.univ : Set X) ∧
          ∀ x : X, ∃ i : ι, ∃ n : ℕ, 0 < n ∧
            ∃ s : Γ(RingedSpace.TensorPower.sheaf (L i) n, ⊤),
              AffineOpenNeighborhood x ((hL i).nonvanishingOpen s) := sorry

/-- Unfolding form of the indexed-family ampleness condition. -/
theorem ampleFamily_iff
    (L : ι → X.Modules)
    [∀ i : ι, Invertible (L i)] :
    AmpleFamily L ↔
      IsCompact (Set.univ : Set X) ∧
        ∀ x : X, ∃ i : ι, ∃ n : ℕ, 0 < n ∧
          ∃ s : Γ(RingedSpace.TensorPower.sheaf (L i) n, ⊤),
            AffineOpenNeighborhood x
              ((inferInstance : Invertible (L i)).nonvanishingOpen s) := sorry

end AlgebraicGeometry.Scheme.Modules
