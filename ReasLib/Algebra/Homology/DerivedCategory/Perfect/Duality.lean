module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Functoriality
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Cohomology
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Unit.Closed
public import ReasLib.CategoryTheory.Monoidal.Closed.Dualizable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfect derived modules and canonical duality

@stack 07VI

This leaf is the module-facing owner for the duality statement in Lemma 15.75.15.  The
canonical object is `RHom(K, A[0])`; an explicit `RHom.ClosedComparison` records the selected
closed/tensor presentation needed for comparison maps.  Carriers and morphisms are concrete;
only perfectness, invertibility, and naturality propositions remain statement-stage obligations.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory.InternalHom
open CategoryTheory.MonoidalCategory
open scoped _root_.DerivedExt

namespace CategoryTheory.DerivedCategory.Perfect.Duality

variable {A : Type u} [CommRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat A))]
variable [BraidedCategory (DerivedCategory (ModuleCat A))]
variable [RHom.Has (A := A)]
variable [DerivedTensor.Right.Has (C := ModuleCat A)]

local notation "DMod" => DerivedCategory (ModuleCat A)

/- The regular degree-zero object is kept as an explicit source object rather than inferred from
an ambient tensor unit. -/

/-- The canonical derived dual `RHom_A(K, A[0])`. -/
@[stacks 07VI "canonical derived dual"]
noncomputable abbrev dual (K : DMod) : DMod :=
  RHom.obj (A := A) K (RHom.Unit.single (A := A))

/-- The contravariant map on canonical derived duals. -/
@[stacks 07VI "derived dual map"]
noncomputable abbrev dualMap {K L : DMod} (f : K ⟶ L) :
    dual (A := A) L ⟶ dual (A := A) K :=
  RHom.map (A := A) f (𝟙 (RHom.Unit.single (A := A)))

/-- The selected closed-owner dual `RHom[M.closed](K, A[0])` used by the textbook-facing
comparison statements. -/
@[stacks 07VI "selected closed-owner derived dual"]
noncomputable abbrev selectedDual
    (M : RHom.ClosedComparison (A := A)) (K : DMod) : DMod :=
  InternalHom.obj M.closed K (RHom.Unit.single (A := A))

/-- The contravariant selected-owner map on source-facing derived duals. -/
@[stacks 07VI "selected closed-owner derived dual map"]
noncomputable abbrev selectedDualMap
    (M : RHom.ClosedComparison (A := A)) {K L : DMod} (f : K ⟶ L) :
    selectedDual M L ⟶ selectedDual M K :=
  (MonoidalClosed.preOf M.closed f).app (RHom.Unit.single (A := A))

/-- The canonical degree-zero `RHom` unit comparison used by tensor/Hom duality. -/
@[stacks 07VI "regular RHom unit comparison"]
noncomputable abbrev unitComparison
    (M : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ DMod) (L : DMod) :
    L ⟶ RHom.obj (A := A) (RHom.Unit.single (A := A)) L :=
  (RHom.Unit.objIsoOf (A := A) (M.adjunction (RHom.Unit.single (A := A)))
    (RHom.Unit.tensorUnitComparisonOf (A := A) M.tensorModel s) L).inv

/-- The evaluation of the canonical derived dual before swapping tensor factors. -/
@[stacks 07VI "derived dual evaluation"]
noncomputable abbrev evaluationDerivedTensor
    (M : RHom.ClosedComparison (A := A)) (K : DMod) :
    (DerivedTensor.Right.functor K).obj (dual (A := A) K) ⟶
      RHom.Unit.single (A := A) :=
  (M.adjunction K).counit.app (RHom.Unit.single (A := A))

/-- The evaluation map with the source factors in the textbook order `K ⊗ Kᵛ`. -/
@[stacks 07VI "source-order derived dual evaluation"]
noncomputable abbrev evaluation
    (M : RHom.ClosedComparison (A := A)) (K : DMod) :
    (DerivedTensor.Right.functor (dual (A := A) K)).obj K ⟶
      RHom.Unit.single (A := A) :=
  (DerivedTensorProduct.comm K (dual (A := A) K)).hom ≫
    evaluationDerivedTensor M K

/-- The canonical bidual comparison `K ⟶ (Kᵛ)ᵛ`. -/
@[stacks 07VI "derived bidual comparison"]
noncomputable abbrev bidualComparison
    (M : RHom.ClosedComparison (A := A)) (K : DMod) :
    K ⟶ dual (A := A) (dual (A := A) K) :=
  (M.adjunction (dual (A := A) K)).homEquiv K (RHom.Unit.single (A := A))
    (evaluation M K)

/-- A perfect derived module has a right-dualizable underlying object for the selected derived
tensor presentation. -/
@[stacks 07VI "perfect object is right-dualizable"]
theorem IsPerfect.isRightDualizable
    (M : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ DMod)
    {K : DMod} (hK : K.IsPerfect) :
    IsRightDualizable K := sorry

/-- The dual of a perfect derived module is perfect. -/
@[stacks 07VI "perfectness of the derived dual"]
theorem IsPerfect.dual_isPerfect
    (M : RHom.ClosedComparison (A := A))
    {K : DMod} (hK : K.IsPerfect) :
    (dual (A := A) K).IsPerfect := sorry

/-- A perfect source has a perfect selected closed-owner dual. -/
@[stacks 07VI "perfectness of the selected derived dual"]
theorem IsPerfect.selectedDual_isPerfect
    (M : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ DMod)
    {K : DMod} (hK : K.IsPerfect) :
    (selectedDual M K).IsPerfect := sorry

/-- The canonical bidual comparison of a perfect object is invertible. -/
@[stacks 07VI "perfect bidual isomorphism"]
theorem bidualComparison_isIso
    (M : RHom.ClosedComparison (A := A))
    {K : DMod} (hK : K.IsPerfect) :
    IsIso (bidualComparison M K) := sorry

/-- The concrete bidual isomorphism obtained from `bidualComparison_isIso`. -/
@[stacks 07VI "concrete perfect bidual isomorphism"]
noncomputable def bidualIso
    (M : RHom.ClosedComparison (A := A))
    {K : DMod} (hK : K.IsPerfect) :
    K ≅ dual (A := A) (dual (A := A) K) :=
  letI := bidualComparison_isIso M hK
  asIso (bidualComparison M K)

/- The selected-H comparison is an intermediate concrete map.  It is kept here because the
canonical `RHom` object and the selected closed object are not definitionally equal. -/

/-- The selected closed-owner tensor/Hom comparison for the regular source object. -/
@[stacks 07VI "selected tensor dual comparison"]
noncomputable def selectedTensorComparison
    (M : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ DMod) (K : DMod) :
    DerivedTensor.Right.functor (InternalHom.obj M.closed K (RHom.Unit.single (A := A))) ⟶
      MonoidalClosed.ihomOf M.closed K where
  app L :=
    (DerivedTensor.Right.functor
      (InternalHom.obj M.closed K (RHom.Unit.single (A := A)))).map
        ((RHom.Unit.ihomObjIso (A := A) M s L).inv) ≫
      DerivedTensor.Right.Closed.compOf M.closed M.tensorModel K
        (RHom.Unit.single (A := A)) L
  naturality {L₁ L₂} f := sorry

/-- The selected tensor/Hom comparison is natural in its target. -/
@[stacks 07VI "selected tensor dual comparison naturality"]
theorem selectedTensorComparison_naturality
    (M : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ DMod) (K : DMod)
    {L₁ L₂ : DMod} (f : L₁ ⟶ L₂) :
    (selectedTensorComparison M s K).app L₁ ≫
        (MonoidalClosed.ihomOf M.closed K).map f =
      (DerivedTensor.Right.functor
        (InternalHom.obj M.closed K (RHom.Unit.single (A := A)))).map f ≫
        (selectedTensorComparison M s K).app L₂ := sorry

/-- The canonical tensor/Hom comparison `L ⊗ᴸ Kᵛ ⟶ RHom(K,L)`. -/
@[stacks 07VI "canonical tensor dual comparison"]
noncomputable def tensorComparison
    (M : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ DMod) (K : DMod) :
    DerivedTensor.Right.functor (dual (A := A) K) ⟶
      RHom.targetFunctor (A := A) K where
  app L :=
    (DerivedTensor.Right.Closed.tensorMapOf M.closed M.tensorModel
      (M.objIso K (RHom.Unit.single (A := A))).hom).app L ≫
      (selectedTensorComparison M s K).app L ≫
      (M.targetIso K).inv.app L
  naturality {L₁ L₂} f := sorry

/-- The tensor/Hom comparison is invertible for a perfect source. -/
@[stacks 07VI "perfect tensor dual comparison isomorphism"]
theorem tensorComparison_isIso
    (M : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ DMod)
    {K : DMod} (hK : K.IsPerfect) :
    IsIso (tensorComparison M s K) := sorry

/-- The concrete functor isomorphism represented by `tensorComparison`. -/
@[stacks 07VI "concrete tensor dual functor isomorphism"]
noncomputable def tensorIso
    (M : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ DMod)
    {K : DMod} (hK : K.IsPerfect) :
    DerivedTensor.Right.functor (dual (A := A) K) ≅
      RHom.targetFunctor (A := A) K :=
  letI := tensorComparison_isIso M s hK
  asIso (tensorComparison M s K)

/-- The degree-zero cohomology map induced by the tensor/Hom comparison. -/
@[stacks 07VI "degree-zero tensor dual comparison"]
noncomputable abbrev tensorZeroCohomologyComparison
    (M : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ DMod) (K L : DMod) :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        ((DerivedTensor.Right.functor (dual (A := A) K)).obj L) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (RHom.obj (A := A) K L) :=
  (DerivedCategory.homologyFunctor (ModuleCat A) 0).map
    ((tensorComparison M s K).app L)

/-- The degree-zero comparison into `Ext⁰` for a perfect source. -/
@[stacks 07VI "degree-zero tensor dual Ext comparison"]
noncomputable def tensorExtZeroComparison
    (M : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ DMod) (K L : DMod) :
    ((DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
      ((DerivedTensor.Right.functor (dual (A := A) K)).obj L)) →ₗ[A]
      Ext⁽(0 : ℤ)⁾(K, L) :=
  (RHom.Cohomology.linearEquiv K L 0).toLinearMap.comp
    (tensorZeroCohomologyComparison M s K L).hom

/-- The degree-zero tensor/Ext comparison is bijective for a perfect source. -/
@[stacks 07VI "degree-zero tensor dual Ext isomorphism"]
theorem tensorExtZeroComparison_bijective
    (M : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ DMod)
    {K : DMod} (hK : K.IsPerfect) (L : DMod) :
    Function.Bijective (tensorExtZeroComparison M s K L) := sorry

/-- The concrete degree-zero linear equivalence from the tensor dual to `Ext⁰`. -/
@[stacks 07VI "concrete degree-zero tensor dual Ext equivalence"]
noncomputable def tensorExtZeroEquiv
    (M : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ DMod)
    {K : DMod} (hK : K.IsPerfect) (L : DMod) :
    ((DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
      ((DerivedTensor.Right.functor (dual (A := A) K)).obj L)) ≃ₗ[A]
      Ext⁽(0 : ℤ)⁾(K, L) :=
  LinearEquiv.ofBijective (tensorExtZeroComparison M s K L)
    (tensorExtZeroComparison_bijective M s hK L)

end CategoryTheory.DerivedCategory.Perfect.Duality

end
