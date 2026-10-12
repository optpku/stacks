/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.KFlat
public import ReasLib.Algebra.Homology.DifferentialGradedModule.BaseChange.Derived.Right
public import ReasLib.Algebra.Homology.DifferentialGradedModule.KFlat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# K-Flat Base Change Comparisons

K-flatness identifies the left- and right-derived models of ordinary base change and makes the
ordinary tensor representative compute relative derived tensor.  The DGA carrier universes for
`A` and `S` are independent; the same-universe restriction belongs only to the restriction-square
model.
-/

@[expose] public section

noncomputable section

universe uR uS uA

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule.BaseChange

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]

/-- K-flatness of `A` makes the canonical comparison from left-derived to right-derived ground
base change invertible. -/
@[stacks 0BYZ "K-flat invertibility of the left-right base-change comparison"]
theorem leftRightComparison_isIso_of_isKFlat
    (A : CochainDGAlgebra.{uR, uA} R) (hA : A.IsKFlat) :
    IsIso (leftRightComparison (S := S) A) := sorry

/-- The canonical isomorphism between the left- and right-derived ground base-change functors
when `A` is K-flat over `R`. -/
@[stacks 0BYZ "left-right derived base-change isomorphism"]
noncomputable def leftRightIso (A : CochainDGAlgebra.{uR, uA} R) (hA : A.IsKFlat) :
    derivedFunctor (S := S) A ≅ rightDerivedFunctor (S := S) A :=
  @asIso _ _ _ _ (leftRightComparison (S := S) A)
    (leftRightComparison_isIso_of_isKFlat (S := S) A hA)

/-- The forward map of `leftRightIso` is the canonical left-to-right comparison. -/
@[simp, stacks 0BYZ "forward map of the left-right derived base-change isomorphism"]
theorem leftRightIso_hom (A : CochainDGAlgebra.{uR, uA} R) (hA : A.IsKFlat) :
    (leftRightIso (S := S) A hA).hom = leftRightComparison (S := S) A := sorry

/-- The inverse map of `leftRightIso` is the canonical inverse of the left-to-right comparison. -/
@[simp, stacks 0BYZ "inverse map of the left-right derived base-change isomorphism"]
theorem leftRightIso_inv (A : CochainDGAlgebra.{uR, uA} R) (hA : A.IsKFlat) :
    (leftRightIso (S := S) A hA).inv =
      @inv _ _ _ _ (leftRightComparison (S := S) A)
        (leftRightComparison_isIso_of_isKFlat (S := S) A hA) := sorry

/-- Lemma 22.33.8 (0BYZ) (1): if `A` is K-flat over `R`, relative derived tensor extension
along `A ⟶ A ⊗[R] S` is canonically isomorphic to the total right derived functor of
`M ↦ M ⊗[R] S`. -/
@[stacks 0BYZ "relative derived tensor as right-derived base change"]
noncomputable def derivedRightIso (A : CochainDGAlgebra.{uR, uA} R) (hA : A.IsKFlat) :
    DifferentialGradedBimodule.Tensor.derivedFunctor (extension (S := S) A) ≅
      rightDerivedFunctor (S := S) A :=
  (derivedIso (S := S) A).symm.trans (leftRightIso (S := S) A hA)

/-- The unit presenting relative derived tensor extension as the right-derived functor of
ordinary ground-ring base change under K-flatness of the DGA. -/
@[stacks 0BYZ "right-derived unit for K-flat relative base change"]
noncomputable def tensorDerivedUnit (A : CochainDGAlgebra.{uR, uA} R) (hA : A.IsKFlat) :
    sourceFunctor (S := S) A ⟶
      DifferentialGradedModule.Derived.Q A ⋙
        DifferentialGradedBimodule.Tensor.derivedFunctor (extension (S := S) A) :=
  rightDerivedUnit (S := S) A ≫
    Functor.whiskerLeft (DifferentialGradedModule.Derived.Q A)
      (derivedRightIso (S := S) A hA).inv

/-- Relative derived tensor with the base-change bimodule satisfies the right-derived universal
property of ordinary ground-ring base change when the DGA is K-flat. -/
@[stacks 0BYZ "relative tensor is the right-derived base-change functor"]
theorem tensorDerived_isRightDerived_of_isKFlat
    (A : CochainDGAlgebra.{uR, uA} R) (hA : A.IsKFlat) :
    (DifferentialGradedBimodule.Tensor.derivedFunctor
      (extension (S := S) A)).IsRightDerivedFunctor
        (tensorDerivedUnit (S := S) A hA)
        (DifferentialGradedModule.quasiIso A) := sorry

/-- Lemma 22.33.8 (0BYZ) (3): if `A` and the underlying `R`-complex of `M` are K-flat, then
`M ⊗[R] S` represents `M ⊗_Aᴸ (A ⊗[R] S)`. -/
@[stacks 0BYZ "K-flat ordinary representative of derived base change"]
theorem representationComparison_isIso_of_isKFlat
    (A : CochainDGAlgebra.{uR, uA} R) (hA : A.IsKFlat)
    (M : DifferentialGradedModule.{uR, max uA uS} A) (hM : M.IsKFlat) :
    IsIso (representationComparison (S := S) A M) := sorry

/-- The canonical isomorphism from relative derived tensor product to the localized ordinary
base-change model under the K-flatness hypotheses. -/
@[stacks 0BYZ "K-flat derived representation isomorphism"]
noncomputable def representationIso
    (A : CochainDGAlgebra.{uR, uA} R) (hA : A.IsKFlat)
    (M : DifferentialGradedModule.{uR, max uA uS} A) (hM : M.IsKFlat) :
    (DifferentialGradedBimodule.Tensor.derivedFunctor (extension (S := S) A)).obj
        ((DifferentialGradedModule.Derived.Q A).obj
          ((DifferentialGradedModule.toK A).obj M)) ≅
      (sourceFunctor (S := S) A).obj ((DifferentialGradedModule.toK A).obj M) :=
  @asIso _ _ _ _ (representationComparison (S := S) A M)
    (representationComparison_isIso_of_isKFlat (S := S) A hA M hM)

/-- The forward map of `representationIso` is the canonical derived representation comparison. -/
@[simp, stacks 0BYZ "forward map of the K-flat derived representation isomorphism"]
theorem representationIso_hom
    (A : CochainDGAlgebra.{uR, uA} R) (hA : A.IsKFlat)
    (M : DifferentialGradedModule.{uR, max uA uS} A) (hM : M.IsKFlat) :
    (representationIso (S := S) A hA M hM).hom =
      representationComparison (S := S) A M := sorry

/-- The inverse map of `representationIso` is the canonical inverse of the representation comparison. -/
@[simp, stacks 0BYZ "inverse map of the K-flat derived representation isomorphism"]
theorem representationIso_inv
    (A : CochainDGAlgebra.{uR, uA} R) (hA : A.IsKFlat)
    (M : DifferentialGradedModule.{uR, max uA uS} A) (hM : M.IsKFlat) :
    (representationIso (S := S) A hA M hM).inv =
      @inv _ _ _ _ (representationComparison (S := S) A M)
        (representationComparison_isIso_of_isKFlat (S := S) A hA M hM) := sorry

end DifferentialGradedModule.BaseChange
