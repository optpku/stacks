module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.ExternalTensor

/-!
# The Künneth formula for scheme cohomology

This module records the cohomological Künneth formula for quasi-compact and quasi-separated
schemes over a field, together with the affine-diagonal variant.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Scheme.Modules
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For quasi-compact schemes over a field whose absolute diagonals are affine, the cohomology
of an external tensor product is isomorphic to the coproduct of tensor products of the
cohomology objects in complementary degrees. -/
theorem cohomologyKunnethOverFieldOfAffineDiagonal
    {k : Type u} [Field k]
    (X Y : Over (Spec (CommRingCat.of k)))
    [CompactSpace X.left.carrier] [CompactSpace Y.left.carrier]
    [IsAffineHom (prod.lift (𝟙 X.left) (𝟙 X.left))]
    [IsAffineHom (prod.lift (𝟙 Y.left) (𝟙 Y.left))]
    (ℱ : X.left.Modules) [ℱ.IsQuasicoherent]
    (𝒢 : Y.left.Modules) [𝒢.IsQuasicoherent]
    (n : ℕ) :
    IsIsomorphic
      (Scheme.Hom.cohomology
        (Limits.pullback.fst X.hom Y.hom ≫ X.hom)
        (externalTensorProduct X.hom Y.hom ℱ 𝒢) n)
      (∐ fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n} ↦
        Scheme.Hom.cohomology X.hom ℱ pq.1.1 ⊗
          Scheme.Hom.cohomology Y.hom 𝒢 pq.1.2) := sorry

/-- For quasi-compact and quasi-separated schemes over a field, the cohomology of an external
tensor product is isomorphic to the coproduct of tensor products of the cohomology objects in
complementary degrees. -/
theorem cohomologyKunnethOverField
    {k : Type u} [Field k]
    (X Y : Over (Spec (CommRingCat.of k)))
    [CompactSpace X.left.carrier] [CompactSpace Y.left.carrier]
    [QuasiSeparatedSpace X.left.carrier] [QuasiSeparatedSpace Y.left.carrier]
    (ℱ : X.left.Modules) [ℱ.IsQuasicoherent]
    (𝒢 : Y.left.Modules) [𝒢.IsQuasicoherent]
    (n : ℕ) :
    IsIsomorphic
      (Scheme.Hom.cohomology
        (Limits.pullback.fst X.hom Y.hom ≫ X.hom)
        (externalTensorProduct X.hom Y.hom ℱ 𝒢) n)
      (∐ fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n} ↦
        Scheme.Hom.cohomology X.hom ℱ pq.1.1 ⊗
          Scheme.Hom.cohomology Y.hom 𝒢 pq.1.2) := sorry

end AlgebraicGeometry.Scheme.Modules
