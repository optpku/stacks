module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Kunneth
import StacksCheckRecall

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

/- Lemma 33.29.1: for quasi-compact schemes over a field whose absolute diagonals are affine,
the cohomology of an external tensor product is the coproduct of tensor products of the
cohomology objects in complementary degrees. -/
@[stacks 0BED] #check
  (AlgebraicGeometry.Scheme.Modules.cohomologyKunnethOverFieldOfAffineDiagonal :
    ∀ {k : Type u} [Field k]
      (X Y : Over (Spec (CommRingCat.of k)))
      [CompactSpace X.left.carrier] [CompactSpace Y.left.carrier]
      [IsAffineHom (prod.lift (𝟙 X.left) (𝟙 X.left))]
      [IsAffineHom (prod.lift (𝟙 Y.left) (𝟙 Y.left))]
      (ℱ : X.left.Modules) [ℱ.IsQuasicoherent]
      (𝒢 : Y.left.Modules) [𝒢.IsQuasicoherent]
      (n : ℕ),
      IsIsomorphic
        (Scheme.Hom.cohomology
          (Limits.pullback.fst X.hom Y.hom ≫ X.hom)
          (externalTensorProduct X.hom Y.hom ℱ 𝒢) n)
        (∐ fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n} ↦
          Scheme.Hom.cohomology X.hom ℱ pq.1.1 ⊗
            Scheme.Hom.cohomology Y.hom 𝒢 pq.1.2))
