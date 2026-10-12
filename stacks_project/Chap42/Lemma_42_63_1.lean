/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Dedekind.ExteriorProduct
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set

universe u

/- Lemma 42.63.1: the exterior product over a locally Dedekind base is a well-defined
ℤ-linear map on the tensor product of degreewise relative Chow groups. -/
@[stacks 0FC4]
#check (AlgebraicGeometry.ChowGroup.Dedekind.exteriorProduct :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (n m : ℤ),
    TensorProduct ℤ (RelativeChow δ X n) (RelativeChow δ Y m) →ₗ[ℤ]
      RelativeChow δ (X ⨯ Y) (n + m - 1))
