module

public import ReasLib.Algebra.Category.ModuleCat.FreeForgetResolution.Generators
public import ReasLib.CategoryTheory.Adjunction.SimplicialResolution.Evaluation
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.UnderlyingHomotopyEquivalence.ModuleCat

/-!
# Contracting the underlying-set free-forgetful resolution

This leaf specializes the canonical postcomposed adjunction contraction to the underlying sets of
free-forgetful module resolutions. Its component formula is expressed through the iterated free
generator owned by `Generators`.
-/

@[expose] public section

open Opposite
open CategoryTheory
open CategoryTheory.SimplicialObject
open AlgebraicTopology
open scoped Simplicial

universe u

namespace CategoryTheory.ModuleCat.FreeForgetResolution

variable (R : Type u) [Ring R]

/-- The simplicial augmentation of an evaluated free-forgetful resolution belongs to the
morphism property detected on underlying simplicial sets. -/
@[stacks 0G5T "free-forgetful augmentation underlying homotopy equivalence"]
theorem evaluation.hom_mem (M : ModuleCat R) :
    SimplicialObject.ModuleCat.underlying.homotopyEquivalences R
      ((evaluation R).obj M).hom := sorry

namespace underlying.set

/-- The degree-zero free-generator section of the underlying-set augmentation. -/
@[stacks 0G5T "underlying-set free-forgetful zero section"]
noncomputable abbrev zeroSection (M : ModuleCat R) :
    (underlying.set R M).right ⟶ (underlying.set R M).left _⦋0⦌ :=
  (Adjunction.SimplicialResolution.postcompose.zeroSection
    (ModuleCat.adj R)).app M

/-- The last extra degeneracy on the underlying-set resolution, obtained by evaluating the
canonical adjunction-level contraction at `M`. -/
@[stacks 0G5T "underlying-set free-forgetful last extra degeneracy"]
noncomputable def lastExtraDegeneracy (M : ModuleCat R) :
    SimplicialObject.Augmented.LastExtraDegeneracy (underlying.set R M) :=
  Adjunction.SimplicialResolution.postcompose.eval.lastExtraDegeneracy
    (ModuleCat.adj R) M

/-- The zero-section of the evaluated last extra degeneracy is the free-generator map. -/
@[simp, stacks 0G5T "underlying-set last extra degeneracy zero-section"]
theorem lastExtraDegeneracy.s' (M : ModuleCat R) :
    (lastExtraDegeneracy R M).s' = zeroSection R M := sorry

/-- The degreewise maps of the evaluated last extra degeneracy are the evaluated unit
insertions. -/
@[simp, stacks 0G5T "underlying-set last extra degeneracy maps"]
theorem lastExtraDegeneracy.s (M : ModuleCat R) (n : ℕ) :
    (lastExtraDegeneracy R M).s n =
      (Adjunction.SimplicialResolution.postcompose.lastDegeneracy
        (ModuleCat.adj R) n).app M := sorry

/-- The inverse of the underlying-set augmentation, obtained by evaluating the canonical
unit-induced inverse for the free-forgetful adjunction. -/
@[stacks 0G5T "underlying-set free-forgetful resolution inverse"]
noncomputable def inverse (M : ModuleCat R) :
    (const (Type u)).obj (underlying.set R M).right ⟶
      (underlying.set R M).left :=
  Adjunction.SimplicialResolution.postcompose.eval.inverse (ModuleCat.adj R) M

namespace inverse

/-- The degree-zero component of the underlying-set inverse is the free-generator section. -/
@[simp, stacks 0G5T "underlying-set free-forgetful inverse in degree zero"]
theorem app_zero (M : ModuleCat R) :
    (underlying.set.inverse R M).app (op ⦋0⦌) = zeroSection R M := sorry

/-- In degree `n`, the underlying-set inverse sends an element to its `(n + 1)`-fold free
generator. -/
@[stacks 0G5T "underlying-set free-forgetful inverse component formula"]
theorem app {R : Type u} [Ring R] (M : ModuleCat R) (n : ℕ) (x : M) :
    (underlying.set.inverse R M).app (op ⦋n⦌) x =
      freeMk.iterate (R := R) M n x := sorry

/-- The free-generator inverse is a strict right inverse to the underlying-set augmentation. -/
@[simp, stacks 0G5T "underlying-set free-forgetful inverse section"]
theorem comp_hom (M : ModuleCat R) :
    inverse R M ≫ (underlying.set R M).hom =
      𝟙 ((const (Type u)).obj (underlying.set R M).right) := sorry

end inverse

/-- The concrete contraction of the underlying-set free-forgetful resolution supplied by its
last extra degeneracy. -/
@[stacks 0G5T "underlying-set free-forgetful resolution contraction"]
noncomputable def homotopy (M : ModuleCat R) :
    SimplicialObject.Homotopy (𝟙 (underlying.set R M).left)
      ((underlying.set R M).hom ≫ inverse R M) :=
  Adjunction.SimplicialResolution.postcompose.eval.homotopy (ModuleCat.adj R) M

/-- The underlying-set free-forgetful resolution as the objectwise specialization of the
canonical adjunction-resolution homotopy equivalence. -/
@[stacks 0G5T "underlying-set free-forgetful resolution homotopy equivalence"]
noncomputable def homotopyEquiv (M : ModuleCat R) :
    HomotopyEquiv (underlying.set R M).left
      ((const (Type u)).obj (underlying.set R M).right) :=
  Adjunction.SimplicialResolution.postcompose.eval.homotopyEquiv
    (ModuleCat.adj R) M

/-- The forward map of the underlying-set specialization is its augmentation. -/
@[simp, stacks 0G5T "underlying-set free-forgetful equivalence forward map"]
theorem homotopyEquiv.hom (M : ModuleCat R) :
    (homotopyEquiv R M).hom = (underlying.set R M).hom := sorry

/-- The inverse map of the underlying-set specialization is the evaluated unit-induced map. -/
@[simp, stacks 0G5T "underlying-set free-forgetful equivalence inverse map"]
theorem homotopyEquiv.inv (M : ModuleCat R) :
    (homotopyEquiv R M).inv = inverse R M := sorry

/-- The underlying-set augmentation of the free-forgetful resolution is a homotopy
equivalence. -/
@[stacks 0G5T "underlying-set free-forgetful augmentation homotopy equivalence"]
theorem isHomotopyEquivalence (M : ModuleCat R) :
    IsHomotopyEquivalence (underlying.set R M).hom := sorry

end underlying.set

end CategoryTheory.ModuleCat.FreeForgetResolution
