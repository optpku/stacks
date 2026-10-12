/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import stacks_project.Chap76.Lemma_76_7_10_Conormal
public import stacks_project.Chap76.Lemma_76_15_12_Differentials

/-!
# Conormal sequence of a formally unramified morphism of algebraic spaces

For a formally unramified morphism `h : Z ⟶ X` of algebraic spaces over `B`,
the `d_{Z'/B}`-induced conormal map of a universal first-order thickening
`i : Z ⟶ Z'` over `X`, transported across the Lemma 76.15.12 isomorphism
`h^* Ω_{X/B} ≃ i^* Ω_{Z'/B}`, and the Lemma 76.7.6 comparison
`h^* Ω_{X/B} ⟶ Ω_{Z/B}` form a right-exact sequence

  `C_{Z/X} ⟶ h^* Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
  (relativeDifferentials idealSheaf idealSheafSubobject)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials

variable {S : Scheme.{u}} {B X Z Z' : AlgebraicSpace S}

/-- The canonical map `C_{Z/X} ⟶ h^* Ω_{X/B}` obtained by transporting the
`d_{Z'/B}`-induced conormal map of the universal first-order thickening
`i : Z ⟶ Z'` along the inverse of `pullbackDifferentialsComparison`. -/
noncomputable def conormalMap (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
    [IsUniversalFirstOrder i h'] [FormallyUnramified h] (w : i ≫ h' = h) :
    (Modules.pullback (IsImmersion.liftCoborder i)).obj
      (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
        (idealSheaf (IsImmersion.liftCoborder i))) ⟶
      (Modules.pullback h).obj (relativeDifferentials f) :=
  Hom.Conormal.Differentials.map i (h' ≫ f) ≫
    inv (pullbackDifferentialsComparison i h' h f w)

/-- `conormalMap` is the coborder `d_{Z'/B}`-induced map followed by the inverse
of `pullbackDifferentialsComparison`. -/
theorem conormalMap_eq (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
    [IsUniversalFirstOrder i h'] [FormallyUnramified h] (w : i ≫ h' = h) :
    conormalMap i h' h f w =
      Hom.Conormal.Differentials.map i (h' ≫ f) ≫
        inv (pullbackDifferentialsComparison i h' h f w) :=
  sorry

/-- Composing the transported conormal map with `pullbackDifferentialsComparison`
recovers the `d_{Z'/B}`-induced conormal map of the thickening. -/
theorem conormalMap_comp_pullbackDifferentialsComparison
    (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
    [IsUniversalFirstOrder i h'] [FormallyUnramified h] (w : i ≫ h' = h) :
    conormalMap i h' h f w ≫ pullbackDifferentialsComparison i h' h f w =
      Hom.Conormal.Differentials.map i (h' ≫ f) :=
  sorry

/-- The canonical comparison `h^* Ω_{X/B} ⟶ Ω_{Z/B}` attached to the identity
square on `B`. -/
noncomputable def comparison (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
    [IsUniversalFirstOrder i h'] [FormallyUnramified h] (w : i ≫ h' = h) :
    (Modules.pullback h).obj (relativeDifferentials f) ⟶
      relativeDifferentials (h ≫ f) :=
  Hom.Differentials.comparison h (𝟙 B) f (h ≫ f)
    (Eq.symm (Category.comp_id (h ≫ f)))

/-- `comparison` is the Lemma 76.7.6 differential comparison of the identity
square on `B`. -/
theorem comparison_eq (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
    [IsUniversalFirstOrder i h'] [FormallyUnramified h] (w : i ≫ h' = h) :
    comparison i h' h f w =
      Hom.Differentials.comparison h (𝟙 B) f (h ≫ f)
        (Eq.symm (Category.comp_id (h ≫ f))) :=
  sorry

/-- The second arrow of the unramified conormal sequence is the Lemma 76.7.6
comparison of the identity square on `B`. -/
theorem comparison_isComparison (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X)
    (f : X ⟶ B) [IsUniversalFirstOrder i h'] [FormallyUnramified h]
    (w : i ≫ h' = h) :
    Hom.Differentials.IsComparison h f (h ≫ f) (comparison i h' h f w) :=
  sorry

/-- The two canonical arrows in the unramified conormal sequence have zero
composite. -/
theorem conormalMap_comp_comparison (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X)
    (f : X ⟶ B) [IsUniversalFirstOrder i h'] [FormallyUnramified h]
    (w : i ≫ h' = h) :
    conormalMap i h' h f w ≫ comparison i h' h f w = 0 :=
  sorry

/-- The canonical conormal short complex associated to a formally unramified
morphism over `B`. -/
noncomputable def complex (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
    [IsUniversalFirstOrder i h'] [FormallyUnramified h] (w : i ≫ h' = h) :
    ShortComplex Z.Modules :=
  ShortComplex.mk (conormalMap i h' h f w) (comparison i h' h f w)
    (conormalMap_comp_comparison i h' h f w)

/-- `complex` is the short complex on `conormalMap` and `comparison`. -/
theorem complex_eq (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
    [IsUniversalFirstOrder i h'] [FormallyUnramified h] (w : i ≫ h' = h) :
    complex i h' h f w =
      ShortComplex.mk (conormalMap i h' h f w) (comparison i h' h f w)
        (conormalMap_comp_comparison i h' h f w) :=
  sorry

/-- The canonical unramified conormal short complex of algebraic spaces is
exact. -/
theorem exact (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
    [IsUniversalFirstOrder i h'] [FormallyUnramified h] (w : i ≫ h' = h) :
    (complex i h' h f w).Exact :=
  sorry

/-- The comparison at the right of the unramified conormal sequence is an
epimorphism. -/
instance comparison_epi (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
    [IsUniversalFirstOrder i h'] [FormallyUnramified h] (w : i ≫ h' = h) :
    Epi (comparison i h' h f w) :=
  sorry

/-- For a formally unramified morphism of algebraic spaces over `B`, the
canonical conormal complex is exact and its right arrow is an epimorphism. -/
theorem exact_and_epi (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
    [IsUniversalFirstOrder i h'] [FormallyUnramified h] (w : i ≫ h' = h) :
    (complex i h' h f w).Exact ∧ Epi (comparison i h' h f w) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials
