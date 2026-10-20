/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Construction
public import ReasLib.Algebra.Category.CommRingCat.Under.FreeAlgebra
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.UnderlyingHomotopyEquivalence.ModuleCat
public import ReasLib.CategoryTheory.Adjunction.SimplicialResolution.Evaluation

/-!
@stack 08NE

# Underlying-set contraction of the polynomial resolution

This leaf owns the iterated-bracket contraction after forgetting the polynomial resolution to
sets. It also exposes the module-view augmentation membership detected by that contraction.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SimplicialObject
open Opposite
open Under
open scoped Simplicial

universe u

namespace CategoryTheory.CommRingCat.Under.PolynomialResolution

variable (A : CommRingCat.{u})

namespace underlying.set

/-- The degree-zero bracket section of the underlying-set augmentation. -/
@[stacks 08NE "underlying polynomial bracket section"]
noncomputable abbrev zeroSection (B : Under A) :
    (underlying.set A B).right ⟶ (underlying.set A B).left _⦋0⦌ :=
  (Adjunction.SimplicialResolution.postcompose.zeroSection
    (adjunction A)).app B

/-- The last extra degeneracy on the underlying-set polynomial resolution, obtained by
evaluating the canonical adjunction-level contraction at `B`. -/
@[stacks 08NE "underlying polynomial last extra degeneracy"]
noncomputable def lastExtraDegeneracy (B : Under A) :
    SimplicialObject.Augmented.LastExtraDegeneracy (underlying.set A B) :=
  Adjunction.SimplicialResolution.postcompose.eval.lastExtraDegeneracy
    (adjunction A) B

/-- The zero-section of the evaluated last extra degeneracy is the bracket map. -/
@[simp, stacks 08NE "underlying polynomial last extra degeneracy zero-section"]
theorem lastExtraDegeneracy.s' (B : Under A) :
    (lastExtraDegeneracy A B).s' = zeroSection A B := sorry

/-- The degreewise maps of the evaluated last extra degeneracy are evaluated unit
insertions. -/
@[simp, stacks 08NE "underlying polynomial last extra degeneracy maps"]
theorem lastExtraDegeneracy.s (B : Under A) (n : ℕ) :
    (lastExtraDegeneracy A B).s n =
      (Adjunction.SimplicialResolution.postcompose.lastDegeneracy
        (adjunction A) n).app B := sorry

/-- The simplicial map whose degreewise values are the iterated brackets of an element of `B`. -/
@[stacks 08NE "underlying polynomial iterated-bracket inverse"]
noncomputable def inverse (B : Under A) :
    (const (Type u)).obj (underlying.set A B).right ⟶ (underlying.set A B).left :=
  Adjunction.SimplicialResolution.postcompose.eval.inverse (adjunction A) B

namespace inverse

/-- The degree-zero component of the underlying-set inverse is the bracket section. -/
@[simp, stacks 08NE "underlying polynomial inverse in degree zero"]
theorem app_zero (B : Under A) :
    (underlying.set.inverse A B).app (op ⦋0⦌) = zeroSection A B := sorry

/-- In degree `n`, the underlying-set inverse sends an element to its `(n + 1)`-fold bracket. -/
@[stacks 08NE "underlying polynomial inverse component formula"]
theorem app {A : CommRingCat.{u}} (B : Under A) (n : ℕ) (x : B.right) :
    (underlying.set.inverse A B).app (op ⦋n⦌) x =
      CommRingCat.Under.FreeAlgebra.generator.iterate (A := A) B n x := sorry

/-- The bracket section is a strict right inverse to the underlying-set augmentation. -/
@[simp, stacks 08NE "underlying polynomial inverse section"]
theorem comp_hom (B : Under A) :
    inverse A B ≫ (underlying.set A B).hom =
      𝟙 ((const (Type u)).obj (underlying.set A B).right) := sorry

end inverse

/-- The concrete contraction of the underlying-set polynomial resolution supplied by its last
extra degeneracy. -/
@[stacks 08NE "underlying polynomial resolution contraction"]
noncomputable def homotopy (B : Under A) :
    SimplicialObject.Homotopy (𝟙 (underlying.set A B).left)
      ((underlying.set A B).hom ≫ inverse A B) :=
  Adjunction.SimplicialResolution.postcompose.eval.homotopy (adjunction A) B

/-- The underlying polynomial resolution with its canonical iterated-bracket homotopy inverse. -/
@[stacks 08NE "polynomial resolution homotopy equivalence with bracket inverse"]
noncomputable def homotopyEquiv (B : Under A) :
    HomotopyEquiv (underlying.set A B).left
      ((const (Type u)).obj (underlying.set A B).right) :=
  Adjunction.SimplicialResolution.postcompose.eval.homotopyEquiv
    (adjunction A) B

/-- The forward map of the underlying-set specialization is its augmentation. -/
@[simp, stacks 08NE "underlying polynomial homotopy-equivalence forward map"]
theorem homotopyEquiv.hom (B : Under A) :
    (homotopyEquiv A B).hom = (underlying.set A B).hom := sorry

/-- The inverse map of the underlying-set specialization is the iterated-bracket map. -/
@[simp, stacks 08NE "underlying polynomial homotopy-equivalence inverse map"]
theorem homotopyEquiv.inv (B : Under A) :
    (homotopyEquiv A B).inv = inverse A B := sorry

/-- The underlying-set augmentation of the polynomial resolution is a homotopy equivalence. -/
@[stacks 08NE "underlying polynomial augmentation homotopy equivalence"]
theorem isHomotopyEquivalence (B : Under A) :
    IsHomotopyEquivalence (underlying.set A B).hom := sorry

end underlying.set

/-- The simplicial augmentation of the module view belongs to the morphism property detected
after forgetting to simplicial sets. -/
@[stacks 08NA "polynomial augmentation underlying homotopy equivalence"]
theorem underlying.module.hom_mem (B : Under A) :
    SimplicialObject.ModuleCat.underlying.homotopyEquivalences A
      (underlying.module A B).hom := sorry

end CategoryTheory.CommRingCat.Under.PolynomialResolution
