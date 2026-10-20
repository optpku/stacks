module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Functoriality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality carried by a closed comparison for canonical `RHom`

This leaf bundles the explicit-owner maps from `InternalHom.Functoriality` at an
`RHom.ClosedComparison`.  It does not infer or install a closed structure, a derived tensor
model, or a parametrized adjunction.

@stack 0E1U
@stack 0A67
@stack 0A8J
@stack 0A6B
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped _root_.DerivedInternalHom

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.ClosedComparison

variable {A : Type u} [CommRing A]
variable [RHom.Has (A := A)]

local notation "D(" A ")" => DerivedCategory (ModuleCat A)

section Monoidal

variable [MonoidalCategory D(A)]

/-- The map of selected internal-Hom objects carried by a closed comparison. -/
@[stacks 0E1U "bundled selected internal-Hom map"]
noncomputable abbrev internalHomMap
    (P : RHom.ClosedComparison (A := A))
    {K₁ K₂ L₁ L₂ : D(A)} (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) :
    RHom[P.closed](K₁, L₁) ⟶ RHom[P.closed](K₂, L₂) :=
  InternalHom.mapOf P.closed fK fL

/-- The selected internal-Hom map with an identity target map is precomposition. -/
@[simp]
theorem internalHomMap_pre
    (P : RHom.ClosedComparison (A := A))
    {K₁ K₂ L : D(A)} (fK : K₂ ⟶ K₁) :
    P.internalHomMap fK (𝟙 L) = (MonoidalClosed.preOf P.closed fK).app L :=
  MonoidalClosed.internalHomMapOf_pre P.closed fK

/-- The selected internal-Hom map with an identity source map is postcomposition. -/
@[simp]
theorem internalHomMap_post
    (P : RHom.ClosedComparison (A := A))
    {K L₁ L₂ : D(A)} (fL : L₁ ⟶ L₂) :
    P.internalHomMap (𝟙 K) fL = (MonoidalClosed.ihomOf P.closed K).map fL :=
  MonoidalClosed.internalHomMapOf_post P.closed fL

/-- The selected internal-Hom map of two identity morphisms is the identity. -/
@[simp]
theorem internalHomMap_id
    (P : RHom.ClosedComparison (A := A)) (K L : D(A)) :
    P.internalHomMap (𝟙 K) (𝟙 L) = 𝟙 _ :=
  MonoidalClosed.internalHomMapOf_id P.closed K L

/-- Selected internal-Hom maps respect composition in both variables. -/
@[reassoc]
theorem internalHomMap_comp
    (P : RHom.ClosedComparison (A := A))
    {K₁ K₂ K₃ L₁ L₂ L₃ : D(A)}
    (fK₁ : K₂ ⟶ K₁) (fK₂ : K₃ ⟶ K₂)
    (fL₁ : L₁ ⟶ L₂) (fL₂ : L₂ ⟶ L₃) :
    P.internalHomMap (fK₂ ≫ fK₁) (fL₁ ≫ fL₂) =
      P.internalHomMap fK₁ fL₁ ≫ P.internalHomMap fK₂ fL₂ :=
  MonoidalClosed.internalHomMapOf_comp P.closed fK₁ fK₂ fL₁ fL₂

/-- Isomorphisms in both variables induce an isomorphism of selected internal-Hom objects. -/
noncomputable abbrev internalHomMapIso
    (P : RHom.ClosedComparison (A := A))
    {K₁ K₂ L₁ L₂ : D(A)} (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) :
    RHom[P.closed](K₁, L₁) ≅ RHom[P.closed](K₂, L₂) :=
  MonoidalClosed.internalHomMapIsoOf P.closed eK eL

/-- The forward map of the selected internal-Hom isomorphism is the corresponding map. -/
@[simp]
theorem internalHomMapIso_hom
    (P : RHom.ClosedComparison (A := A))
    {K₁ K₂ L₁ L₂ : D(A)} (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) :
    (P.internalHomMapIso eK eL).hom = P.internalHomMap eK.hom eL.hom :=
  MonoidalClosed.internalHomMapIsoOf_hom P.closed eK eL

/-- The inverse map of the selected internal-Hom isomorphism is induced by the inverse maps. -/
@[simp]
theorem internalHomMapIso_inv
    (P : RHom.ClosedComparison (A := A))
    {K₁ K₂ L₁ L₂ : D(A)} (eK : K₂ ≅ K₁) (eL : L₁ ≅ L₂) :
    (P.internalHomMapIso eK eL).inv = P.internalHomMap eK.inv eL.inv :=
  MonoidalClosed.internalHomMapIsoOf_inv P.closed eK eL

end Monoidal

section Braided

variable [MonoidalCategory D(A)] [BraidedCategory D(A)]
variable [DerivedTensor.Right.Has (C := ModuleCat.{u} A)]

/-- The coherent map of canonical fixed-right derived tensor functors carried by `P`. -/
@[stacks 064M "bundled derived tensor parameter map"]
noncomputable abbrev derivedTensorProductMap
    (P : RHom.ClosedComparison (A := A))
    {L₁ L₂ : D(A)} (f : L₁ ⟶ L₂) :
    DerivedTensor.Right.functor L₁ ⟶ DerivedTensor.Right.functor L₂ :=
  InternalHom.tensorMapOf P.closed P.tensorModel f

/-- The selected derived-tensor parameter map sends identities to identities. -/
@[simp]
theorem derivedTensorProductMap_id
    (P : RHom.ClosedComparison (A := A)) (L : D(A)) :
    P.derivedTensorProductMap (𝟙 L) = 𝟙 (DerivedTensor.Right.functor L) :=
  DerivedTensor.Right.Closed.tensorMapOf_id P.closed P.tensorModel L

/-- The selected derived-tensor parameter map respects composition. -/
@[reassoc]
theorem derivedTensorProductMap_comp
    (P : RHom.ClosedComparison (A := A))
    {L₁ L₂ L₃ : D(A)} (f : L₁ ⟶ L₂) (g : L₂ ⟶ L₃) :
    P.derivedTensorProductMap (f ≫ g) =
      P.derivedTensorProductMap f ≫ P.derivedTensorProductMap g :=
  DerivedTensor.Right.Closed.tensorMapOf_comp P.closed P.tensorModel f g

/-- The selected derived-tensor parameter map is compatible with the objectwise tensor model. -/
@[reassoc]
theorem derivedTensorProductMap_objIsoTensor
    (P : RHom.ClosedComparison (A := A))
    {L₁ L₂ : D(A)} (f : L₁ ⟶ L₂) (K : D(A)) :
    (P.derivedTensorProductMap f).app K ≫
        (DerivedTensor.Right.Monoidal.Model.objIsoTensor P.tensorModel K L₂).hom =
      (DerivedTensor.Right.Monoidal.Model.objIsoTensor P.tensorModel K L₁).hom ≫
        (𝟙 K ⊗ₘ f) :=
  InternalHom.tensorMapOf_objIsoTensor P.closed P.tensorModel f K

/-- Source-order composition of selected internal-Hom objects carried by `P`. -/
@[stacks 0A8J "bundled derived internal-Hom composition"]
noncomputable abbrev derivedInternalHomComp
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    DerivedTensor.Right.obj (RHom[P.closed](L, M)) (RHom[P.closed](K, L)) ⟶
      RHom[P.closed](K, M) :=
  InternalHom.compOf P.closed P.tensorModel K L M

/-- The bundled internal-Hom composition is the canonical composition carried by `P`. -/
@[simp]
theorem derivedInternalHomComp_eq
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    P.derivedInternalHomComp K L M =
      InternalHom.compOf P.closed P.tensorModel K L M := rfl

/-- Formula for bundled internal-Hom composition through the selected tensor model. -/
theorem derivedInternalHomComp_spec
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    P.derivedInternalHomComp K L M =
      (DerivedTensor.Right.Monoidal.Model.objIsoTensor P.tensorModel
        (RHom[P.closed](L, M)) (RHom[P.closed](K, L))).hom ≫
        MonoidalClosed.Source.compOf P.closed K L M :=
  DerivedTensor.Right.Closed.compOf_spec P.closed P.tensorModel K L M

/-- Bundled internal-Hom composition is natural in its target. -/
theorem derivedInternalHomComp_natural_target
    (P : RHom.ClosedComparison (A := A)) (K L : D(A))
    {M₁ M₂ : D(A)} (f : M₁ ⟶ M₂) :
    CommSq
      ((DerivedTensor.Right.functor (RHom[P.closed](K, L))).map
        (P.internalHomMap (𝟙 L) f))
      (P.derivedInternalHomComp K L M₁)
      (P.derivedInternalHomComp K L M₂)
      (P.internalHomMap (𝟙 K) f) :=
  InternalHom.compOf_natural_target P.closed P.tensorModel K L f

/-- Bundled internal-Hom composition is natural in its source. -/
theorem derivedInternalHomComp_natural_source
    (P : RHom.ClosedComparison (A := A))
    {K₁ K₂ : D(A)} (f : K₁ ⟶ K₂) (L M : D(A)) :
    CommSq
      ((P.derivedTensorProductMap (P.internalHomMap f (𝟙 L))).app
        (RHom[P.closed](L, M)))
      (P.derivedInternalHomComp K₂ L M)
      (P.derivedInternalHomComp K₁ L M)
      (P.internalHomMap f (𝟙 M)) :=
  InternalHom.compOf_natural_source P.closed P.tensorModel f L M

/-- Bundled internal-Hom composition is natural in its middle object. -/
theorem derivedInternalHomComp_natural_middle
    (P : RHom.ClosedComparison (A := A))
    (K : D(A)) {L₁ L₂ : D(A)} (g : L₁ ⟶ L₂) (M : D(A)) :
    CommSq
      ((DerivedTensor.Right.functor (RHom[P.closed](K, L₁))).map
        (P.internalHomMap g (𝟙 M)))
      ((P.derivedTensorProductMap (P.internalHomMap (𝟙 K) g)).app
        (RHom[P.closed](L₂, M)))
      (P.derivedInternalHomComp K L₁ M)
      (P.derivedInternalHomComp K L₂ M) :=
  InternalHom.compOf_natural_middle P.closed P.tensorModel K g M

/-- The tensor-left/internal-Hom comparison carried by `P`. -/
@[stacks 0BYN "bundled tensor-left internal-Hom comparison"]
noncomputable abbrev tensorLeftComparison
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    DerivedTensor.Right.obj K (RHom[P.closed](M, L)) ⟶
      RHom[P.closed](M, DerivedTensor.Right.obj K L) :=
  InternalHom.TensorLeft.comparisonOf P.closed P.tensorModel K L M

/-- Formula for the bundled tensor-left/internal-Hom comparison. -/
theorem tensorLeftComparison_spec
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    P.tensorLeftComparison K L M =
      (DerivedTensor.Right.Monoidal.Model.objIsoTensor
        P.tensorModel K ((MonoidalClosed.ihomOf P.closed M).obj L)).hom ≫
        MonoidalClosed.TensorInternalHom.comparisonOf P.closed K L M ≫
        (MonoidalClosed.ihomOf P.closed M).map
          (DerivedTensor.Right.Monoidal.Model.objIsoTensor P.tensorModel K L).inv :=
  DerivedTensor.Right.Closed.TensorInternalHom.comparisonOf_spec
    P.closed P.tensorModel K L M

/-- The tensor-left comparison is natural in the tensor factor. -/
theorem tensorLeftComparison_natural_tensor
    (P : RHom.ClosedComparison (A := A))
    {K₁ K₂ L M : D(A)} (fK : K₁ ⟶ K₂) :
    CommSq
      ((DerivedTensor.Right.functor (RHom[P.closed](M, L))).map fK)
      (P.tensorLeftComparison K₁ L M)
      (P.tensorLeftComparison K₂ L M)
      (P.internalHomMap (𝟙 M) ((DerivedTensor.Right.functor L).map fK)) :=
  InternalHom.TensorLeft.comparisonOf_natural_tensor P.closed P.tensorModel fK

/-- The tensor-left comparison is natural in the internal-Hom target. -/
theorem tensorLeftComparison_natural_target
    (P : RHom.ClosedComparison (A := A))
    (K M : D(A)) {L₁ L₂ : D(A)} (fL : L₁ ⟶ L₂) :
    CommSq
      ((P.derivedTensorProductMap (P.internalHomMap (𝟙 M) fL)).app K)
      (P.tensorLeftComparison K L₁ M)
      (P.tensorLeftComparison K L₂ M)
      (P.internalHomMap (𝟙 M) ((P.derivedTensorProductMap fL).app K)) :=
  InternalHom.TensorLeft.comparisonOf_natural_target P.closed P.tensorModel K M fL

/-- The tensor-left comparison is natural in the internal-Hom source. -/
theorem tensorLeftComparison_natural_source
    (P : RHom.ClosedComparison (A := A))
    (K L : D(A)) {M₁ M₂ : D(A)} (fM : M₁ ⟶ M₂) :
    CommSq
      ((P.derivedTensorProductMap (P.internalHomMap fM (𝟙 L))).app K)
      (P.tensorLeftComparison K L M₂)
      (P.tensorLeftComparison K L M₁)
      (P.internalHomMap fM (𝟙 (DerivedTensor.Right.obj K L))) :=
  InternalHom.TensorLeft.comparisonOf_natural_source P.closed P.tensorModel K L fM

/-- The tensor-right/internal-Hom comparison carried by `P`. -/
@[stacks 0A67 "bundled tensor-right internal-Hom comparison"]
noncomputable abbrev tensorRightComparison
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    DerivedTensor.Right.obj (RHom[P.closed](L, M)) K ⟶
      RHom[P.closed](RHom[P.closed](K, L), M) :=
  InternalHom.TensorRight.comparisonOf P.closed P.tensorModel K L M

/-- Formula for the bundled tensor-right/internal-Hom comparison. -/
theorem tensorRightComparison_spec
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    P.tensorRightComparison K L M =
      (DerivedTensor.Right.Monoidal.Model.objIsoTensor P.tensorModel
        ((MonoidalClosed.ihomOf P.closed L).obj M) K).hom ≫
        MonoidalClosed.TensorRight.comparisonOf P.closed K L M :=
  InternalHom.TensorRight.comparisonOf_spec P.closed P.tensorModel K L M

/-- The tensor-right comparison is natural in the tensor factor. -/
theorem tensorRightComparison_natural_tensor
    (P : RHom.ClosedComparison (A := A))
    {K₁ K₂ L M : D(A)} (fK : K₁ ⟶ K₂) :
    CommSq
      ((P.derivedTensorProductMap fK).app (RHom[P.closed](L, M)))
      (P.tensorRightComparison K₁ L M)
      (P.tensorRightComparison K₂ L M)
      (P.internalHomMap (P.internalHomMap fK (𝟙 L)) (𝟙 M)) :=
  InternalHom.TensorRight.comparisonOf_natural_tensor P.closed P.tensorModel fK

/-- The tensor-right comparison is natural in its middle object. -/
theorem tensorRightComparison_natural_middle
    (P : RHom.ClosedComparison (A := A))
    (K : D(A)) {L₁ L₂ M : D(A)} (fL : L₁ ⟶ L₂) :
    CommSq
      ((DerivedTensor.Right.functor K).map (P.internalHomMap fL (𝟙 M)))
      (P.tensorRightComparison K L₂ M)
      (P.tensorRightComparison K L₁ M)
      (P.internalHomMap (P.internalHomMap (𝟙 K) fL) (𝟙 M)) :=
  InternalHom.TensorRight.comparisonOf_natural_middle P.closed P.tensorModel K fL

/-- The tensor-right comparison is natural in its target. -/
theorem tensorRightComparison_natural_target
    (P : RHom.ClosedComparison (A := A))
    (K L : D(A)) {M₁ M₂ : D(A)} (fM : M₁ ⟶ M₂) :
    CommSq
      ((DerivedTensor.Right.functor K).map (P.internalHomMap (𝟙 L) fM))
      (P.tensorRightComparison K L M₁)
      (P.tensorRightComparison K L M₂)
      (P.internalHomMap (𝟙 (RHom[P.closed](K, L))) fM) :=
  InternalHom.TensorRight.comparisonOf_natural_target P.closed P.tensorModel K L fM

/-- The unit of the selected fixed-right tensor/internal-Hom adjunction carried by `P`. -/
@[stacks 0A6B "bundled derived tensor internal-Hom unit"]
noncomputable abbrev unitOf
    (P : RHom.ClosedComparison (A := A)) (K L : D(A)) :
    K ⟶ RHom[P.closed](L, DerivedTensor.Right.obj K L) :=
  InternalHom.unitOf P.closed P.tensorModel K L

/-- The selected tensor/internal-Hom unit is natural in its left input. -/
@[reassoc]
theorem unitOf_natural_left
    (P : RHom.ClosedComparison (A := A))
    (L : D(A)) {K₁ K₂ : D(A)} (f : K₁ ⟶ K₂) :
    f ≫ P.unitOf K₂ L =
      P.unitOf K₁ L ≫
        P.internalHomMap (𝟙 L) ((DerivedTensor.Right.functor L).map f) :=
  InternalHom.unitOf_natural_left P.closed P.tensorModel L f

/-- The selected tensor/internal-Hom unit is natural in its right input. -/
theorem unitOf_natural_right
    (P : RHom.ClosedComparison (A := A))
    (K : D(A)) {L₁ L₂ : D(A)} (f : L₁ ⟶ L₂) :
    CommSq
      (P.unitOf K L₂)
      (P.unitOf K L₁)
      (P.internalHomMap f (𝟙 (DerivedTensor.Right.obj K L₂)))
      (P.internalHomMap (𝟙 L₁) ((P.derivedTensorProductMap f).app K)) :=
  InternalHom.unitOf_natural_right P.closed P.tensorModel K f

/-- The counit of the selected fixed-right tensor/internal-Hom adjunction carried by `P`. -/
@[stacks 0A6B "bundled derived tensor internal-Hom counit"]
noncomputable abbrev counitOf
    (P : RHom.ClosedComparison (A := A)) (E N : D(A)) :
    DerivedTensor.Right.obj (RHom[P.closed](E, N)) E ⟶ N :=
  InternalHom.counitOf P.closed P.tensorModel E N

/-- The selected tensor/internal-Hom counit is natural in its target. -/
@[reassoc]
theorem counitOf_natural_target
    (P : RHom.ClosedComparison (A := A))
    (E : D(A)) {N₁ N₂ : D(A)} (f : N₁ ⟶ N₂) :
    (DerivedTensor.Right.functor E).map (P.internalHomMap (𝟙 E) f) ≫
        P.counitOf E N₂ = P.counitOf E N₁ ≫ f :=
  InternalHom.counitOf_natural_target P.closed P.tensorModel E f

/-- The selected tensor/internal-Hom counit is natural in its source. -/
theorem counitOf_natural_source
    (P : RHom.ClosedComparison (A := A))
    {E₁ E₂ : D(A)} (f : E₁ ⟶ E₂) (N : D(A)) :
    CommSq
      ((P.derivedTensorProductMap f).app (RHom[P.closed](E₂, N)))
      ((DerivedTensor.Right.functor E₁).map (P.internalHomMap f (𝟙 N)))
      (P.counitOf E₂ N)
      (P.counitOf E₁ N) :=
  InternalHom.counitOf_natural_source P.closed P.tensorModel f N

/-! The remaining declarations expose the parametrized-adjunction calculus already determined by
the same `ClosedComparison`.  They introduce no second tensor map or adjunction owner. -/

/-- The selected internal Hom is right adjoint to canonical fixed-right derived tensoring. -/
@[stacks 064M "bundled fixed-right derived tensor adjunction"]
noncomputable abbrev selectedAdjunction
    (P : RHom.ClosedComparison (A := A)) (L : D(A)) :
    DerivedTensor.Right.functor L ⊣ MonoidalClosed.ihomOf P.closed L :=
  InternalHom.adjunctionOf P.closed P.tensorModel L

/-- The bundled unit is the unit component of the selected fixed-right adjunction. -/
@[simp, stacks 0A6B, stacks 0A8W "bundled derived tensor unit specification"]
theorem unitOf_spec
    (P : RHom.ClosedComparison (A := A)) (K L : D(A)) :
    P.unitOf K L = (P.selectedAdjunction L).unit.app K :=
  DerivedTensor.Right.Closed.unitOf_spec P.closed P.tensorModel K L

/-- The bundled counit is the counit component of the selected fixed-right adjunction. -/
@[simp, stacks 0A8W "bundled derived tensor counit specification"]
theorem counitOf_spec
    (P : RHom.ClosedComparison (A := A)) (E N : D(A)) :
    P.counitOf E N = (P.selectedAdjunction E).counit.app N :=
  DerivedTensor.Right.Closed.counitOf_spec P.closed P.tensorModel E N

/-- Under the selected adjunction, changing the right tensor factor is the mate of
precomposition on the selected internal Hom. -/
@[stacks 064M "bundled derived tensor parameter mate"]
theorem derivedTensorProductMap_homEquiv
    (P : RHom.ClosedComparison (A := A))
    {L₁ L₂ : D(A)} (f : L₁ ⟶ L₂) (K : D(A)) :
    (P.selectedAdjunction L₁).homEquiv K
        ((DerivedTensor.Right.functor L₂).obj K)
        ((P.derivedTensorProductMap f).app K) =
      (P.selectedAdjunction L₂).unit.app K ≫
        (MonoidalClosed.preOf P.closed f).app
          ((DerivedTensor.Right.functor L₂).obj K) :=
  MonoidalClosed.leftAdjointMapOf_homEquiv P.closed
    (fun L => P.selectedAdjunction L) f K

/-- Inverse-mate formula for the bundled right-factor map and an arbitrary transpose. -/
@[reassoc, stacks 064M "bundled derived tensor inverse mate"]
theorem derivedTensorProductMap_homEquiv_symm
    (P : RHom.ClosedComparison (A := A))
    {L₁ L₂ : D(A)} (f : L₁ ⟶ L₂) {K N : D(A)}
    (g : K ⟶ (MonoidalClosed.ihomOf P.closed L₂).obj N) :
    (P.derivedTensorProductMap f).app K ≫
        ((P.selectedAdjunction L₂).homEquiv K N).symm g =
      ((P.selectedAdjunction L₁).homEquiv K N).symm
        (g ≫ (MonoidalClosed.preOf P.closed f).app N) :=
  MonoidalClosed.leftAdjointMapOf_homEquiv_symm P.closed
    (fun L => P.selectedAdjunction L) f g

/-- Arbitrary-map parameter naturality for the bundled right-factor map. -/
@[reassoc, stacks 064M "bundled derived tensor mate naturality"]
theorem derivedTensorProductMap_homEquiv_naturality
    (P : RHom.ClosedComparison (A := A))
    {L₁ L₂ : D(A)} (f : L₁ ⟶ L₂) {K N : D(A)}
    (g : (DerivedTensor.Right.functor L₂).obj K ⟶ N) :
    (P.selectedAdjunction L₁).homEquiv K N
        ((P.derivedTensorProductMap f).app K ≫ g) =
      (P.selectedAdjunction L₂).homEquiv K N g ≫
        (MonoidalClosed.preOf P.closed f).app N :=
  MonoidalClosed.leftAdjointMapOf_homEquiv_naturality P.closed
    (fun L => P.selectedAdjunction L) f g

/-- An isomorphism of right tensor factors induces an explicit natural isomorphism of the
canonical fixed-right derived tensor functors. -/
@[stacks 064M "bundled derived tensor parameter isomorphism"]
noncomputable def derivedTensorProductMapIso
    (P : RHom.ClosedComparison (A := A)) {L₁ L₂ : D(A)} (e : L₁ ≅ L₂) :
    DerivedTensor.Right.functor L₁ ≅ DerivedTensor.Right.functor L₂ :=
  MonoidalClosed.leftAdjointMapIsoOf P.closed
    (fun L => P.selectedAdjunction L) e

/-- The forward map of the bundled derived-tensor parameter isomorphism. -/
@[simp]
theorem derivedTensorProductMapIso_hom
    (P : RHom.ClosedComparison (A := A)) {L₁ L₂ : D(A)} (e : L₁ ≅ L₂) :
    (P.derivedTensorProductMapIso e).hom = P.derivedTensorProductMap e.hom :=
  MonoidalClosed.leftAdjointMapIsoOf_hom P.closed
    (fun L => P.selectedAdjunction L) e

/-- The inverse map of the bundled derived-tensor parameter isomorphism. -/
@[simp]
theorem derivedTensorProductMapIso_inv
    (P : RHom.ClosedComparison (A := A)) {L₁ L₂ : D(A)} (e : L₁ ≅ L₂) :
    (P.derivedTensorProductMapIso e).inv = P.derivedTensorProductMap e.inv :=
  MonoidalClosed.leftAdjointMapIsoOf_inv P.closed
    (fun L => P.selectedAdjunction L) e

/-- The generated curried derived-tensor functor determined by the pointwise adjunctions in
`P`.  Its morphisms in the outer variable are the bundled mate maps. -/
@[stacks 064M "bundled generated derived tensor functor"]
noncomputable abbrev selectedTensorFunctor
    (P : RHom.ClosedComparison (A := A)) : D(A) ⥤ D(A) ⥤ D(A) :=
  DerivedTensor.Right.Closed.Generated.functorOf P.closed P.tensorModel

/-- The genuine parametrized adjunction generated by `P`. -/
@[stacks 064M "bundled generated derived tensor adjunction"]
noncomputable abbrev selectedAdjunction₂
    (P : RHom.ClosedComparison (A := A)) :
    P.selectedTensorFunctor ⊣₂ MonoidalClosed.internalHomOf P.closed :=
  DerivedTensor.Right.Closed.Generated.adj₂Of P.closed P.tensorModel

/-- The selected tensor bifunctor restricts objectwise to fixed-right derived tensoring. -/
@[simp]
theorem selectedTensorFunctor_obj
    (P : RHom.ClosedComparison (A := A)) (L : D(A)) :
    P.selectedTensorFunctor.obj L = DerivedTensor.Right.functor L :=
  DerivedTensor.Right.Closed.Generated.functorOf_obj P.closed P.tensorModel L

/-- The selected tensor bifunctor maps outer morphisms by the bundled parameter map. -/
@[simp]
theorem selectedTensorFunctor_map
    (P : RHom.ClosedComparison (A := A))
    {L₁ L₂ : D(A)} (f : L₁ ⟶ L₂) :
    P.selectedTensorFunctor.map f = P.derivedTensorProductMap f :=
  DerivedTensor.Right.Closed.Generated.functorOf_map P.closed P.tensorModel f

/-- The parametrized selected adjunction restricts to the selected pointwise adjunction. -/
@[simp]
theorem selectedAdjunction₂_adj
    (P : RHom.ClosedComparison (A := A)) (L : D(A)) :
    P.selectedAdjunction₂.adj L = P.selectedAdjunction L :=
  DerivedTensor.Right.Closed.Generated.adj₂Of_adj P.closed P.tensorModel L

end Braided

end CategoryTheory.DerivedCategory.InternalHom.RHom.ClosedComparison
