module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Finite fibre powers and configuration opens

This file constructs the finite fibre power of a scheme morphism and its open locus on which
the coordinate points are pairwise distinct.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiberPower

variable {X Y : Scheme.{u}}

/-- The `n`-fold fibre power of `f : Y ⟶ X`, represented as the finite product of `Over.mk f`
in the slice category `Over X`. -/
noncomputable abbrev obj (f : Y ⟶ X) (n : ℕ) : Over X :=
  ∏ᶜ fun _ : Fin n ↦ Over.mk f

/-- The coordinate projection from an `n`-fold fibre power to its source scheme. -/
noncomputable def projection (f : Y ⟶ X) {n : ℕ} (i : Fin n) :
    (obj f n).left ⟶ Y :=
  (Pi.π (fun _ : Fin n ↦ Over.mk f) i).left

/-- Every coordinate projection of a fibre power is a morphism over the common base. -/
@[reassoc]
theorem projection_comp (f : Y ⟶ X) {n : ℕ} (i : Fin n) :
    projection f i ≫ f = (obj f n).hom := sorry

/-- The locus in a finite fibre power where distinct coordinates have distinct images is open. -/
theorem isOpen_pairwiseDistinct (f : Y ⟶ X) (n : ℕ) [IsSeparated f] :
    IsOpen {x : (obj f n).left |
      ∀ i j : Fin n, i ≠ j → projection f i x ≠ projection f j x} := sorry

/-- The open locus in a finite fibre power on which all coordinate points are pairwise distinct. -/
noncomputable def configurationOpen (f : Y ⟶ X) (n : ℕ) [IsSeparated f] :
    (obj f n).left.Opens where
  carrier := {x | ∀ i j : Fin n, i ≠ j → projection f i x ≠ projection f j x}
  is_open' := isOpen_pairwiseDistinct f n

/-- Membership in the configuration open means that every pair of distinct coordinate indices
has distinct images in `Y`. -/
theorem mem_configurationOpen (f : Y ⟶ X) (n : ℕ) [IsSeparated f]
    (x : (obj f n).left) :
    x ∈ configurationOpen f n ↔
      ∀ i j : Fin n, i ≠ j → projection f i x ≠ projection f j x := sorry

/-- The canonical morphism from the pairwise-distinct configuration open to the base scheme. -/
noncomputable def configurationToBase (f : Y ⟶ X) (n : ℕ) [IsSeparated f] :
    (configurationOpen f n).toScheme ⟶ X :=
  (configurationOpen f n).ι ≫ (obj f n).hom

/-- The configuration morphism to the base is the open inclusion followed by the fibre-power
structure morphism. -/
theorem configurationToBase_def (f : Y ⟶ X) (n : ℕ) [IsSeparated f] :
    configurationToBase f n = (configurationOpen f n).ι ≫ (obj f n).hom := sorry

end AlgebraicGeometry.Scheme.Hom.FiberPower
