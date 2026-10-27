/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Differentials
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.Differentials
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.Existence

/-!
# Conormal sequence of a formally unramified morphism of algebraic spaces

The conormal map of a universal first-order thickening, transported along the
pullback-differentials comparison, gives a right-exact sequence
`C_{Z/X} ⟶ h^* Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0` for a formally unramified morphism
`h : Z ⟶ X` over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom (relativeDifferentials)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials

variable {S : Scheme.{u}} {B X Z Z' : AlgebraicSpace S}

/-- The canonical map `C_{Z/X} ⟶ h^* Ω_{X/B}` obtained by transporting the
`d_{Z'/B}`-induced conormal map of the universal first-order thickening
`i : Z ⟶ Z'` along the inverse of `pullbackDifferentialsComparison`. -/
noncomputable def conormalMap (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
    [IsUniversalFirstOrder i h'] [FormallyUnramified h] (w : i ≫ h' = h) :
    Hom.conormalSheaf i ⟶ (Modules.pullback h).obj (relativeDifferentials f) :=
  Hom.Conormal.Differentials.map i (h' ≫ f) ≫
    inv (pullbackDifferentialsComparison i h' h f w)

/-- Composing the transported conormal map with `pullbackDifferentialsComparison`
recovers the `d_{Z'/B}`-induced conormal map of the thickening. -/
theorem conormalMap_comp_pullbackDifferentialsComparison
    (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
    [IsUniversalFirstOrder i h'] [FormallyUnramified h] (w : i ≫ h' = h) :
    conormalMap i h' h f w ≫ pullbackDifferentialsComparison i h' h f w =
      Hom.Conormal.Differentials.map i (h' ≫ f) := sorry

/-- The transported conormal map followed by the canonical differential
comparison has zero composite. -/
theorem conormalMap_comp_comparison (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X)
    (f : X ⟶ B) [IsUniversalFirstOrder i h'] [FormallyUnramified h]
    (w : i ≫ h' = h) :
    conormalMap i h' h f w ≫
      Hom.Differentials.comparison h (𝟙 B) f (h ≫ f)
        (Eq.symm (Category.comp_id (h ≫ f))) = 0 := sorry

/-- The canonical conormal short complex associated to a formally unramified
morphism over `B`, presented by a universal first-order thickening. -/
noncomputable def complex (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
    [IsUniversalFirstOrder i h'] [FormallyUnramified h] (w : i ≫ h' = h) :
    ShortComplex Z.Modules :=
  ShortComplex.mk (conormalMap i h' h f w)
    (Hom.Differentials.comparison h (𝟙 B) f (h ≫ f)
      (Eq.symm (Category.comp_id (h ≫ f))))
    (conormalMap_comp_comparison i h' h f w)

/-- The canonical unramified conormal short complex of algebraic spaces is
exact. -/
theorem exact (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
    [IsUniversalFirstOrder i h'] [FormallyUnramified h] (w : i ≫ h' = h) :
    (complex i h' h f w).Exact := sorry

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Differentials

variable {S : Scheme.{u}} {B X Z : AlgebraicSpace S}

/-- The canonical differential comparison for a formally unramified morphism
over `B` is an epimorphism. -/
instance comparison_epi_of_formallyUnramified (h : Z ⟶ X) (f : X ⟶ B)
    [FormallyUnramified h] :
    Epi (comparison h (𝟙 B) f (h ≫ f)
      (Eq.symm (Category.comp_id (h ≫ f)))) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Differentials

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials

variable {S : Scheme.{u}} {B X Z Z' : AlgebraicSpace S}

/-- For a formally unramified morphism of algebraic spaces over `B`, the
canonical conormal complex is exact and its right arrow is an epimorphism. -/
theorem exact_and_epi (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
    [IsUniversalFirstOrder i h'] [FormallyUnramified h] (w : i ≫ h' = h) :
    (complex i h' h f w).Exact ∧
      Epi (Hom.Differentials.comparison h (𝟙 B) f (h ≫ f)
        (Eq.symm (Category.comp_id (h ≫ f)))) := sorry

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials
