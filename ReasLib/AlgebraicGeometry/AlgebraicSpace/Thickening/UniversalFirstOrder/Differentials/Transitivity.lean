/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.Functorial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.ConormalSequence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Glueing

/-!
# Conormal-differentials transitivity for formally unramified morphisms

A commutative triangle of algebraic spaces with formally unramified morphisms
`Z ⟶ X` and `Z ⟶ Y` has a canonical right-exact sequence
`C_{Z/Y} ⟶ C_{Z/X} ⟶ i^* Ω_{X/Y} ⟶ 0`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials.Transitivity

variable {S : Scheme.{u}}
variable {X Y Z ZX ZY : AlgebraicSpace S}

/-- The conormal comparison `C_{Z/Y} ⟶ C_{Z/X}` induced by a commutative triangle,
using universal first-order thickenings and the inverse identity-pullback comparison. -/
noncomputable def projection (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY) (fY : ZY ⟶ Y)
    (f : X ⟶ Y) [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
    [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)]
    (sq : CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f) :
    Hom.conormalSheaf iY ⟶ Hom.conormalSheaf iX :=
  (SmallEtaleModuleGlueing.modulesPullbackId Z).inv.app (Hom.conormalSheaf iY) ≫
    IsUniversalFirstOrder.conormalMap iX fX iY fY (𝟙 Z) f sq

/-- The conormal comparison followed by the canonical conormal-to-differentials
map has zero composite. -/
theorem projection_comp_conormalMap (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY)
    (fY : ZY ⟶ Y) (f : X ⟶ Y)
    [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
    [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)]
    (sq : CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f) :
    projection iX fX iY fY f sq ≫
      IsUniversalFirstOrder.Differentials.conormalMap iX fX (iX ≫ fX) f rfl = 0 := sorry

/-- The canonical conormal-differentials short complex of a commutative triangle
whose two morphisms from `Z` are formally unramified. -/
noncomputable def complex (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY) (fY : ZY ⟶ Y)
    (f : X ⟶ Y) [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
    [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)]
    (sq : CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f) :
    ShortComplex Z.Modules :=
  ShortComplex.mk (projection iX fX iY fY f sq)
    (IsUniversalFirstOrder.Differentials.conormalMap iX fX (iX ≫ fX) f rfl)
    (projection_comp_conormalMap iX fX iY fY f sq)

/-- The canonical conormal-differentials short complex of two formally unramified
morphisms of algebraic spaces is exact. -/
theorem exact (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY) (fY : ZY ⟶ Y)
    (f : X ⟶ Y) [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
    [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)]
    (sq : CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f) :
    (complex iX fX iY fY f sq).Exact := sorry

/-- The canonical map `C_{Z/X} ⟶ i^* Ω_{X/Y}` is an epimorphism when both
`i : Z ⟶ X` and its composite with `X ⟶ Y` are formally unramified. -/
instance conormalMap_epi (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (f : X ⟶ Y)
    [IsUniversalFirstOrder iX fX] [FormallyUnramified (iX ≫ fX)]
    [FormallyUnramified ((iX ≫ fX) ≫ f)] :
    Epi (IsUniversalFirstOrder.Differentials.conormalMap iX fX (iX ≫ fX) f rfl) := sorry

/-- For a commutative triangle with formally unramified morphisms `Z ⟶ X` and
`Z ⟶ Y`, the canonical sequence `C_{Z/Y} ⟶ C_{Z/X} ⟶ i^* Ω_{X/Y} ⟶ 0` is exact. -/
theorem exact_and_epi (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY) (fY : ZY ⟶ Y)
    (f : X ⟶ Y) [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
    [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)]
    (sq : CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f) :
    (complex iX fX iY fY f sq).Exact ∧
      Epi (IsUniversalFirstOrder.Differentials.conormalMap iX fX (iX ≫ fX) f rfl) := sorry

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials.Transitivity
