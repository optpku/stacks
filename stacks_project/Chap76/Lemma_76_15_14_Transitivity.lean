/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import stacks_project.Chap76.Lemma_76_15_13_ConormalSequence
public import stacks_project.Chap76.Lemma_76_15_14_Comparison

/-!
# Conormal-differentials transitivity for two formally unramified morphisms

A commutative triangle of algebraic spaces with formally unramified morphisms
`Z ⟶ X` and `Z ⟶ Y` yields a right-exact sequence
`C_{Z/Y} ⟶ C_{Z/X} ⟶ i^* Ω_{X/Y} ⟶ 0`. The first arrow is identity-pullback
transport of the Lemma 76.15.8 comparison, imported from the Comparison sibling.
The second arrow is the Lemma 76.15.13 conormal-to-differentials map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom (relativeDifferentials)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials
namespace Transitivity

variable {S : Scheme.{u}}
variable {X Y Z ZX ZY : AlgebraicSpace S}

/-- The second arrow `C_{Z/X} ⟶ i^* Ω_{X/Y}` of the two-unramified-morphisms
sequence, as the Lemma 76.15.13 conormal map of the universal first-order
thickening of `Z` over `X`. -/
noncomputable def map (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY) (fY : ZY ⟶ Y)
    (f : X ⟶ Y) [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
    [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)]
    (sq : CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f) :
    conormal iX ⟶
      (Modules.pullback (iX ≫ fX)).obj (relativeDifferentials f) :=
  conormalMap iX fX (iX ≫ fX) f rfl

/-- `map` is the Lemma 76.15.13 conormal-to-differentials map of the thickening
of `Z` over `X`. -/
theorem map_eq (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY) (fY : ZY ⟶ Y)
    (f : X ⟶ Y) [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
    [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)]
    (sq : CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f) :
    map iX fX iY fY f sq = conormalMap iX fX (iX ≫ fX) f rfl :=
  sorry

/-- The two canonical arrows in the two-unramified-morphisms sequence have zero
composite. -/
theorem projection_comp_map (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY)
    (fY : ZY ⟶ Y) (f : X ⟶ Y)
    [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
    [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)]
    (sq : CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f) :
    projection iX fX iY fY f sq ≫ map iX fX iY fY f sq = 0 :=
  sorry

/-- The canonical conormal-differentials short complex of two formally unramified
morphisms of algebraic spaces. -/
noncomputable def complex (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY) (fY : ZY ⟶ Y)
    (f : X ⟶ Y) [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
    [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)]
    (sq : CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f) :
    ShortComplex Z.Modules :=
  ShortComplex.mk (projection iX fX iY fY f sq) (map iX fX iY fY f sq)
    (projection_comp_map iX fX iY fY f sq)

/-- `complex` is the short complex on `projection` and `map`. -/
theorem complex_eq (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY) (fY : ZY ⟶ Y)
    (f : X ⟶ Y) [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
    [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)]
    (sq : CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f) :
    complex iX fX iY fY f sq =
      ShortComplex.mk (projection iX fX iY fY f sq) (map iX fX iY fY f sq)
        (projection_comp_map iX fX iY fY f sq) :=
  sorry

/-- The canonical two-unramified-morphisms short complex of algebraic spaces is
exact. -/
theorem exact (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY) (fY : ZY ⟶ Y)
    (f : X ⟶ Y) [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
    [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)]
    (sq : CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f) :
    (complex iX fX iY fY f sq).Exact :=
  sorry

/-- The map `C_{Z/X} ⟶ i^* Ω_{X/Y}` in the two-unramified-morphisms sequence is an
epimorphism. -/
instance map_epi (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY) (fY : ZY ⟶ Y)
    (f : X ⟶ Y) [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
    [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)]
    (sq : CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f) :
    Epi (map iX fX iY fY f sq) :=
  sorry

/-- For formally unramified morphisms `Z ⟶ X` and `Z ⟶ Y` of algebraic spaces, the
canonical sequence `C_{Z/Y} ⟶ C_{Z/X} ⟶ i^* Ω_{X/Y} ⟶ 0` is exact. -/
theorem exact_and_epi (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY) (fY : ZY ⟶ Y)
    (f : X ⟶ Y) [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
    [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)]
    (sq : CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f) :
    (complex iX fX iY fY f sq).Exact ∧ Epi (map iX fX iY fY f sq) :=
  sorry

end Transitivity
end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials
