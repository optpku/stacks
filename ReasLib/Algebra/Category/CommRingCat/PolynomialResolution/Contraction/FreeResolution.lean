/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Construction
public import ReasLib.Algebra.Category.CommRingCat.Under.FreeAlgebra
public import ReasLib.CategoryTheory.Adjunction.SimplicialResolution.Evaluation

/-!
@stack 08NE

# Contraction of free polynomial resolutions

This leaf owns the structured contraction of the polynomial resolution evaluated on a free
`A`-algebra. The shared resolution and generator data remain in their canonical owner leaves.
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

namespace freeResolution

/-- The degree-zero bracket map for the polynomial resolution of a free `A`-algebra. -/
@[stacks 08NE "free-algebra bracket section"]
noncomputable abbrev zeroSection (E : Type u) :
    ((freeResolution A).obj E).right ⟶ ((freeResolution A).obj E).left _⦋0⦌ :=
  (Adjunction.SimplicialResolution.precompose.zeroSection
    (adjunction A)).app E

/-- The extra degeneracy on the polynomial resolution of a free algebra, obtained by evaluating
the canonical precomposed adjunction contraction at `E`. -/
@[stacks 08NE "free-algebra polynomial extra degeneracy"]
noncomputable def extraDegeneracy (E : Type u) :
    SimplicialObject.Augmented.ExtraDegeneracy ((freeResolution A).obj E) :=
  Adjunction.SimplicialResolution.precompose.eval.extraDegeneracy
    (adjunction A) E

/-- The zero-section of the evaluated extra degeneracy is the free-algebra bracket map. -/
@[simp, stacks 08NE "free-algebra extra degeneracy zero-section"]
theorem extraDegeneracy.s' (E : Type u) :
    (extraDegeneracy A E).s' = zeroSection A E := sorry

/-- The degreewise maps of the evaluated extra degeneracy are evaluated unit insertions. -/
@[simp, stacks 08NE "free-algebra extra degeneracy maps"]
theorem extraDegeneracy.s (E : Type u) (n : ℕ) :
    (extraDegeneracy A E).s n =
      (Adjunction.SimplicialResolution.precompose.extraDegeneracyMap
        (adjunction A) n).app E := sorry

/-- The simplicial `A`-algebra map obtained by iterating the bracket map on generators. -/
@[stacks 08NE "free-algebra iterated-bracket inverse"]
noncomputable def inverse (E : Type u) :
    (const (Under A)).obj ((freeResolution A).obj E).right ⟶ ((freeResolution A).obj E).left :=
  Adjunction.SimplicialResolution.precompose.eval.inverse (adjunction A) E

namespace inverse

/-- The degree-zero component of the free-algebra inverse is the bracket section. -/
@[simp, stacks 08NE "free-algebra inverse in degree zero"]
theorem app_zero (E : Type u) :
    (freeResolution.inverse A E).app (op ⦋0⦌) = zeroSection A E := sorry

/-- In degree `n`, the structured inverse sends a free generator to its `(n + 1)`-fold
bracket. -/
@[stacks 08NE "free-algebra inverse on generators"]
theorem app_generator {E : Type u} (n : ℕ) (e : E) :
    ((freeResolution.inverse A E).app (op ⦋n⦌)).right
        (CommRingCat.Under.FreeAlgebra.generator A e) =
      CommRingCat.Under.FreeAlgebra.generator.iterate (A := A)
        ((freeResolution A).obj E).right n
        (CommRingCat.Under.FreeAlgebra.generator A e) := sorry

/-- The free-algebra bracket map is a strict right inverse to the resolution augmentation. -/
@[simp, stacks 08NE "free-algebra inverse section"]
theorem comp_hom (E : Type u) :
    inverse A E ≫ ((freeResolution A).obj E).hom =
      𝟙 ((const (Under A)).obj ((freeResolution A).obj E).right) := sorry

end inverse

/-- The concrete contraction of the free-algebra polynomial resolution supplied by its extra
degeneracy. -/
@[stacks 08NE "free-algebra polynomial resolution contraction"]
noncomputable def homotopy (E : Type u) :
    SimplicialObject.Homotopy
      (((freeResolution A).obj E).hom ≫ inverse A E)
        (𝟙 ((freeResolution A).obj E).left) :=
  Adjunction.SimplicialResolution.precompose.eval.homotopy (adjunction A) E

/-- The resolution of a free `A`-algebra with its canonical iterated-bracket homotopy equivalence. -/
@[stacks 08NE "free-algebra resolution homotopy equivalence"]
noncomputable def homotopyEquiv (E : Type u) :
    HomotopyEquiv ((freeResolution A).obj E).left
      ((const (Under A)).obj ((freeResolution A).obj E).right) :=
  Adjunction.SimplicialResolution.precompose.eval.homotopyEquiv
    (adjunction A) E

/-- The forward map of the free-algebra specialization is its augmentation. -/
@[simp, stacks 08NE "free-algebra homotopy-equivalence forward map"]
theorem homotopyEquiv.hom (E : Type u) :
    (homotopyEquiv A E).hom = ((freeResolution A).obj E).hom := sorry

/-- The inverse map of the free-algebra specialization is the iterated-bracket map. -/
@[simp, stacks 08NE "free-algebra homotopy-equivalence inverse map"]
theorem homotopyEquiv.inv (E : Type u) :
    (homotopyEquiv A E).inv = inverse A E := sorry

/-- The augmentation of the polynomial resolution of a free algebra is a homotopy
equivalence. -/
@[stacks 08NE "free-algebra resolution augmentation homotopy equivalence"]
theorem isHomotopyEquivalence (E : Type u) :
    IsHomotopyEquivalence ((freeResolution A).obj E).hom := sorry

end freeResolution

end CategoryTheory.CommRingCat.Under.PolynomialResolution
