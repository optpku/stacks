module

public import stacks_project.Chap75.Lemma_75_21_1_Criteria
public import stacks_project.Chap75.Lemma_75_21_3_InternalHom
public import stacks_project.Chap75.Lemma_75_21_3_Pullback
public import stacks_project.Chap75.Lemma_75_21_3_Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Closed
public import ReasLib.CategoryTheory.Functor.Derived.TensorComparison

/-!
# Inheritance of cohomology base change under derived tensor and internal Hom

On a cartesian square of algebraic spaces, the equivalent conditions of Lemma 75.21.1
pass from `L(g')^* K ⟶ K'` to the induced maps after `- ⊗^L K` and after `RHom(E, -)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory CategoryTheory.DerivedCategory.DerivedTensor
open CategoryTheory.Functor.LeftDerived
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed hiding id
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Lemma 75.21.3 (1): on a cartesian square of algebraic spaces over a scheme `S`, if
`K` is in `D_QCoh(𝒪_X)` and `L(g')^* K ⟶ K'` satisfies the equivalent conditions of
Lemma 75.21.1, then for `E` in `D_QCoh(𝒪_X)` those conditions hold for
`L(g')^*(E ⊗^L K) ⟶ L(g')^* E ⊗^L K'`. -/
@[stacks 0DKI]
theorem cohomologyBaseChange_tensor {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [(ModuleDerived.pullback g').Monoidal]
    (T_X : @Right.Monoidal.Model (Modules X) _ _ _ _ _ _ _)
    (T_X' : @Right.Monoidal.Model (Modules X') _ _ _ _ _ _ _)
    (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (E : DerivedQCoh X) (hα : cohomologyBaseChangeHolds sq K K' α) :
    cohomologyBaseChangeHolds sq (tensorObj E K) (tensorObj (pullbackObj g' E) K')
      (tensorBaseChangeMap g' T_X T_X' E K K' α) :=
  sorry

namespace DerivedTensorPullback

/-- The totalized tensor bifunctor on complexes of module sheaves. -/
noncomputable abbrev complexTensor {S : Scheme.{u}} (X : AlgebraicSpace S) :
    CochainComplex (Modules X) ℤ × CochainComplex (Modules X) ℤ ⥤
      CochainComplex (Modules X) ℤ :=
  Functor.uncurry.obj (curriedTensor (Modules X)).map₂CochainComplex

/-- The tensor bifunctor of complexes is the ordinary totalized module tensor. -/
theorem complexTensor_obj {S : Scheme.{u}} (X : AlgebraicSpace S)
    (leftComplex rightComplex : CochainComplex (Modules X) ℤ) :
    (complexTensor X).obj (leftComplex, rightComplex) =
      HomologicalComplex.tensorObj leftComplex rightComplex := sorry

end DerivedTensorPullback

/-- Compatibility with derived module tensor and its canonical pullback comparison.
The tensor counits exhibit the ambient tensors as derived totalized module tensor.
The raw comparison is fixed on every summand by ordinary module pullback, and the
derived tensorator is fixed by its counit equation and the iterated universal property.
No cohomology-base-change conclusion is included in this interface. -/
structure DerivedTensorPullback.{uSpace} {S : Scheme.{uSpace}} {X' X : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived X')]
    (g' : X' ⟶ X) [(ModuleDerived.pullback g').Monoidal] where
  /-- Fixed-right derived tensor model on the source. -/
  sourceModel : @Right.Monoidal.Model (Modules X) _ _ _ _ _ _ _
  /-- Fixed-right derived tensor model on the target. -/
  targetModel : @Right.Monoidal.Model (Modules X') _ _ _ _ _ _ _
  /-- Comparison from derived to ordinary tensor on source complexes. -/
  sourceCounit :
    (DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X).prod
        DerivedCategory.Q ⋙
        tensor (ModuleDerived X) ⟶
      DerivedTensorPullback.complexTensor X ⋙ DerivedCategory.Q
  /-- Comparison from derived to ordinary tensor on target complexes. -/
  targetCounit :
    (DerivedCategory.Q : CochainComplex (Modules X') ℤ ⥤ ModuleDerived X').prod
        DerivedCategory.Q ⋙
        tensor (ModuleDerived X') ⟶
      DerivedTensorPullback.complexTensor X' ⋙ DerivedCategory.Q
  /-- The source tensor satisfies the two-variable derived universal property. -/
  sourceIsRightKanExtension :
    (tensor (ModuleDerived X)).IsRightKanExtension sourceCounit
  /-- The target tensor satisfies the two-variable derived universal property. -/
  targetIsRightKanExtension :
    (tensor (ModuleDerived X')).IsRightKanExtension targetCounit
  /-- Ordinary tensor-pullback comparison on complexes. -/
  rawComparison :
    DerivedTensorPullback.complexTensor X ⋙
        (Modules.pullback g').mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      ((Modules.pullback g').mapHomologicalComplex (ComplexShape.up ℤ)).prod
          ((Modules.pullback g').mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
        DerivedTensorPullback.complexTensor X'
  /-- On each total-degree summand, the raw map is canonical module pullback tensor. -/
  rawComparison_spec (leftComplex rightComplex : CochainComplex (Modules X) ℤ)
      (leftDegree rightDegree totalDegree : ℤ) (hdegree : leftDegree + rightDegree = totalDegree) :
    (Modules.pullback g').map
        (HomologicalComplex.ιTensorObj leftComplex rightComplex
          leftDegree rightDegree totalDegree hdegree) ≫
        (rawComparison.app (leftComplex, rightComplex)).f totalDegree =
      Modules.DirectTensorComparison.pullbackTensor g'
          (leftComplex.X leftDegree) (rightComplex.X rightDegree) ≫
        HomologicalComplex.ιTensorObj
          (((Modules.pullback g').mapHomologicalComplex (ComplexShape.up ℤ)).obj leftComplex)
          (((Modules.pullback g').mapHomologicalComplex (ComplexShape.up ℤ)).obj rightComplex)
          leftDegree rightDegree totalDegree hdegree
  /-- Tensoring the two derived pullbacks computes the iterated left derived functor. -/
  targetIteratedIsRightKanExtension :
    ((ModuleDerived.pullback g').prod (ModuleDerived.pullback g') ⋙
        tensor (ModuleDerived X')).IsRightKanExtension
      (TensorComparison.targetCounit
        (DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X)
        (DerivedCategory.Q : CochainComplex (Modules X') ℤ ⥤ ModuleDerived X')
        ((Modules.pullback g').mapHomologicalComplex (ComplexShape.up ℤ))
        (ModuleDerived.pullback g') (DerivedTensorPullback.complexTensor X')
        (tensor (ModuleDerived X'))
        (Homotopy.cochainCounit (Modules.pullback g')) targetCounit)
  /-- The inverse tensorator is the derived comparison of the canonical raw map. -/
  comparison_counit (leftComplex rightComplex : CochainComplex (Modules X) ℤ) :
    (Functor.Monoidal.μIso (ModuleDerived.pullback g')
        (DerivedCategory.Q.obj leftComplex) (DerivedCategory.Q.obj rightComplex)).inv ≫
        ((Homotopy.cochainCounit (Modules.pullback g')).app leftComplex ⊗ₘ
          (Homotopy.cochainCounit (Modules.pullback g')).app rightComplex) ≫
        targetCounit.app
          (((Modules.pullback g').mapHomologicalComplex (ComplexShape.up ℤ)).obj leftComplex,
            ((Modules.pullback g').mapHomologicalComplex (ComplexShape.up ℤ)).obj rightComplex) =
      (ModuleDerived.pullback g').map (sourceCounit.app (leftComplex, rightComplex)) ≫
        (Homotopy.cochainCounit (Modules.pullback g')).app
          (HomologicalComplex.tensorObj leftComplex rightComplex) ≫
        DerivedCategory.Q.map (rawComparison.app (leftComplex, rightComplex))

/-- Fixed-parameter right adjoints of canonical derived tensoring, with quasi-coherent values.
Right-adjoint uniqueness identifies each presentation with derived sheaf Hom.
The recovered closed presentations below identify the comparison with the canonical
pullback/internal-Hom mate; no additional comparison hypothesis is required. -/
structure DerivedInternalHomPullback.{uSpace} {S : Scheme.{uSpace}}
    {X' X : AlgebraicSpace S} [MonoidalCategory (ModuleDerived X)]
    [MonoidalCategory (ModuleDerived X')] (g' : X' ⟶ X)
    [(ModuleDerived.pullback g').Monoidal] extends DerivedTensorPullback g' where
  /-- The canonical derived `RHom` functor on the source presentation. -/
  sourceRHom : ModuleDerived X → ModuleDerived X ⥤ ModuleDerived X
  /-- The canonical derived `RHom` functor on the target presentation. -/
  targetRHom : ModuleDerived X' → ModuleDerived X' ⥤ ModuleDerived X'
  /-- The source `RHom` adjunction for each fixed first variable. -/
  sourceRHomAdjunction (E : ModuleDerived X) :
    DerivedTensor.Right.functor E ⊣ sourceRHom E
  /-- The target `RHom` adjunction for each fixed first variable. -/
  targetRHomAdjunction (E : ModuleDerived X') :
    DerivedTensor.Right.functor E ⊣ targetRHom E
  /-- Source `RHom` from a perfect complex preserves quasi-coherence. -/
  sourceRHom_mem_of_isPerfect (E : ModuleDerived X) (K : DerivedQCoh X)
      (hE : ModuleDerived.IsPerfect E) :
    derivedQuasiCoherentModuleProperty X ((sourceRHom E).obj K.obj)
  /-- Target `RHom` from a pulled-back perfect complex preserves quasi-coherence. -/
  targetRHom_mem_of_isPerfect (E : ModuleDerived X) (K' : DerivedQCoh X')
      (hE : ModuleDerived.IsPerfect E) :
    derivedQuasiCoherentModuleProperty X'
      ((targetRHom ((ModuleDerived.pullback g').obj E)).obj K'.obj)
  /-- Source `RHom` from a pseudo-coherent complex into a bounded-below object preserves
  quasi-coherence. -/
  sourceRHom_mem_of_isPseudoCoherent (E : ModuleDerived X) (K : DerivedQCoh X)
      (hE : IsPseudoCoherent X E)
      (hK : (t.plus : ObjectProperty (ModuleDerived X)) K.obj) :
    derivedQuasiCoherentModuleProperty X ((sourceRHom E).obj K.obj)
  /-- Target `RHom` from a pulled-back pseudo-coherent complex into the given target preserves
  quasi-coherence under the base-change hypotheses. -/
  targetRHom_mem_of_isPseudoCoherent {Y' Y : AlgebraicSpace S}
      (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback g' f' f g)
      (K : DerivedQCoh X) (K' : DerivedQCoh X')
      (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
      (hα : cohomologyBaseChangeHolds sq K K' α)
      (hK : (t.plus : ObjectProperty (ModuleDerived X)) K.obj)
      (E : ModuleDerived X) (hE : IsPseudoCoherent X E) :
    derivedQuasiCoherentModuleProperty X'
      ((targetRHom ((ModuleDerived.pullback g').obj E)).obj K'.obj)

/-- Construct a selected derived tensor/internal-Hom comparison presentation. -/
def DerivedInternalHomPullback.of
    {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived X')]
    (g' : X' ⟶ X) [(ModuleDerived.pullback g').Monoidal]
    (tensorModel : DerivedTensorPullback g')
    (sourceRHom : ModuleDerived X → ModuleDerived X ⥤ ModuleDerived X)
    (targetRHom : ModuleDerived X' → ModuleDerived X' ⥤ ModuleDerived X')
    (sourceRHomAdjunction : (E : ModuleDerived X) →
      DerivedTensor.Right.functor E ⊣ sourceRHom E)
    (targetRHomAdjunction : (E : ModuleDerived X') →
      DerivedTensor.Right.functor E ⊣ targetRHom E)
    (sourceRHom_mem_of_isPerfect : (E : ModuleDerived X) → (K : DerivedQCoh X) →
      ModuleDerived.IsPerfect E →
        derivedQuasiCoherentModuleProperty X ((sourceRHom E).obj K.obj))
    (targetRHom_mem_of_isPerfect : (E : ModuleDerived X) → (K' : DerivedQCoh X') →
      ModuleDerived.IsPerfect E →
        derivedQuasiCoherentModuleProperty X'
          ((targetRHom ((ModuleDerived.pullback g').obj E)).obj K'.obj))
    (sourceRHom_mem_of_isPseudoCoherent : (E : ModuleDerived X) → (K : DerivedQCoh X) →
      IsPseudoCoherent X E → (t.plus : ObjectProperty (ModuleDerived X)) K.obj →
        derivedQuasiCoherentModuleProperty X ((sourceRHom E).obj K.obj))
    (targetRHom_mem_of_isPseudoCoherent : {Y' Y : AlgebraicSpace S} →
      (f' : X' ⟶ Y') → (f : X ⟶ Y) → (g : Y' ⟶ Y) →
      (sq : IsPullback g' f' f g) → (K : DerivedQCoh X) → (K' : DerivedQCoh X') →
      (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') →
      (hα : cohomologyBaseChangeHolds sq K K' α) →
      (hK : (t.plus : ObjectProperty (ModuleDerived X)) K.obj) →
      (E : ModuleDerived X) → IsPseudoCoherent X E →
        derivedQuasiCoherentModuleProperty X'
          ((targetRHom ((ModuleDerived.pullback g').obj E)).obj K'.obj)) :
    DerivedInternalHomPullback g' :=
  { toDerivedTensorPullback := tensorModel
    sourceRHom := sourceRHom
    targetRHom := targetRHom
    sourceRHomAdjunction := sourceRHomAdjunction
    targetRHomAdjunction := targetRHomAdjunction
    sourceRHom_mem_of_isPerfect := sourceRHom_mem_of_isPerfect
    targetRHom_mem_of_isPerfect := targetRHom_mem_of_isPerfect
    sourceRHom_mem_of_isPseudoCoherent := sourceRHom_mem_of_isPseudoCoherent
    targetRHom_mem_of_isPseudoCoherent := targetRHom_mem_of_isPseudoCoherent }

namespace DerivedInternalHomPullback

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]

/-- Recover the closed structure represented by fixed-right derived tensor adjunctions. -/
@[implicit_reducible]
noncomputable def closedOf (M : @Right.Monoidal.Model (Modules X) _ _ _ _ _ _ _)
    (R : ModuleDerived X → ModuleDerived X ⥤ ModuleDerived X)
    (adj : ∀ E, Right.functor E ⊣ R E) : MonoidalClosed (ModuleDerived X) where
  closed E :=
    { rightAdj := R E
      adj := (adj E).ofNatIsoLeft (M.functorIsoTensorRight E ≪≫
        NatIso.ofComponents (fun K ↦ β_ K E)
          (fun {_ _} f ↦ BraidedCategory.braiding_naturality_left f E)) }

private theorem closedOf_curry (M : @Right.Monoidal.Model (Modules X) _ _ _ _ _ _ _)
    (R : ModuleDerived X → ModuleDerived X ⥤ ModuleDerived X)
    (adj : ∀ E, Right.functor E ⊣ R E) (E K N : ModuleDerived X)
    (f : K ⊗ E ⟶ N) :
    braidedHomEquivOf (closedOf M R adj) K E N f =
      (adj E).homEquiv K N ((M.objIsoTensor K E).hom ≫ f) := by
  change ((adj E).ofNatIsoLeft
    (_ : Right.functor E ≅ MonoidalCategory.tensorLeft E)).homEquiv
    K N ((β_ K E).inv ≫ f ≫ 𝟙 N) = _
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  change (adj E).homEquiv K N
    (((M.objIsoTensor K E).hom ≫ (β_ K E).hom) ≫
      ((β_ K E).inv ≫ f ≫ 𝟙 N)) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id]

private theorem closedOf_evaluation (M : @Right.Monoidal.Model (Modules X) _ _ _ _ _ _ _)
    (R : ModuleDerived X → ModuleDerived X ⥤ ModuleDerived X)
    (adj : ∀ E, Right.functor E ⊣ R E) (E N : ModuleDerived X) :
    (β_ ((R E).obj N) E).hom ≫
      (MonoidalClosed.adjunctionOf (closedOf M R adj) E).counit.app N =
      (M.objIsoTensor ((R E).obj N) E).inv ≫ (adj E).counit.app N := by
  change (β_ ((R E).obj N) E).hom ≫
    (((β_ ((R E).obj N) E).inv ≫ (M.objIsoTensor ((R E).obj N) E).inv) ≫
      (adj E).counit.app N) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

variable {X' : AlgebraicSpace S}
variable [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]

/-- The source closed presentation determined by the actual derived-tensor adjunctions. -/
@[implicit_reducible]
noncomputable def sourceClosed {g' : X' ⟶ X} [(ModuleDerived.pullback g').Monoidal]
    (model : DerivedInternalHomPullback g') : MonoidalClosed (ModuleDerived X) :=
  closedOf model.sourceModel model.sourceRHom model.sourceRHomAdjunction

/-- The target closed presentation determined by the actual derived-tensor adjunctions. -/
@[implicit_reducible]
noncomputable def targetClosed {g' : X' ⟶ X} [(ModuleDerived.pullback g').Monoidal]
    (model : DerivedInternalHomPullback g') : MonoidalClosed (ModuleDerived X') :=
  closedOf model.targetModel model.targetRHom model.targetRHomAdjunction

end DerivedInternalHomPullback

namespace DerivedTensorPullback

variable {S : Scheme.{u}} {X' X : AlgebraicSpace S}
variable [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]

/-- Replace the fixed-right realizations while retaining the same canonical
two-variable tensor counits and pullback comparison. -/
noncomputable def withModels (g' : X' ⟶ X)
    [(ModuleDerived.pullback g').Monoidal] (model : DerivedTensorPullback g')
    (sourceModel : @Right.Monoidal.Model (Modules X) _ _ _ _ _ _ _)
    (targetModel : @Right.Monoidal.Model (Modules X') _ _ _ _ _ _ _) :
    DerivedTensorPullback g' :=
  { model with sourceModel := sourceModel, targetModel := targetModel }

/-- Changing fixed-right realizations leaves the tensor-pullback counit unchanged. -/
theorem withModels_sourceCounit (g' : X' ⟶ X)
    [(ModuleDerived.pullback g').Monoidal] (model : DerivedTensorPullback g')
    (sourceModel : @Right.Monoidal.Model (Modules X) _ _ _ _ _ _ _)
    (targetModel : @Right.Monoidal.Model (Modules X') _ _ _ _ _ _ _) :
    (withModels g' model sourceModel targetModel).sourceCounit = model.sourceCounit := sorry

/-- The internal-Hom comparison is the mate for the actual fixed-right derived tensors,
followed by the given map of target complexes. -/
noncomputable def internalHomMap (g' : X' ⟶ X)
    [(ModuleDerived.pullback g').Monoidal] (model : DerivedInternalHomPullback g')
    (E : ModuleDerived X) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj K.obj ⟶ K'.obj)
    (h_source : derivedQuasiCoherentModuleProperty X
      ((model.sourceRHom E).obj K.obj))
    (h_target : derivedQuasiCoherentModuleProperty X'
      ((model.targetRHom ((ModuleDerived.pullback g').obj E)).obj K'.obj)) :
    (ModuleDerived.pullback g').obj
        (internalHomObj (model.sourceRHom E) K h_source).obj ⟶
      (internalHomObj (model.targetRHom ((ModuleDerived.pullback g').obj E))
        K' h_target).obj :=
  (model.targetRHomAdjunction ((ModuleDerived.pullback g').obj E)).homEquiv
    ((ModuleDerived.pullback g').obj ((model.sourceRHom E).obj K.obj)) K'.obj
    ((model.toDerivedTensorPullback.targetModel.objIsoTensor
        ((ModuleDerived.pullback g').obj ((model.sourceRHom E).obj K.obj))
        ((ModuleDerived.pullback g').obj E)).hom ≫
      (Functor.Monoidal.μIso (ModuleDerived.pullback g')
        ((model.sourceRHom E).obj K.obj) E).hom ≫
      (ModuleDerived.pullback g').map
        ((model.toDerivedTensorPullback.sourceModel.objIsoTensor
          ((model.sourceRHom E).obj K.obj) E).inv) ≫
      (ModuleDerived.pullback g').map
        ((model.sourceRHomAdjunction E).counit.app K.obj) ≫ α)

set_option backward.isDefEq.respectTransparency false in
/-- The fixed-right mate is exactly the source-order canonical pullback/internal-Hom
comparison followed by covariance in `α`, in its recovered closed presentations. -/
theorem internalHomMap_eq_comparison (g' : X' ⟶ X)
    [(ModuleDerived.pullback g').Monoidal] (model : DerivedInternalHomPullback g')
    (E : ModuleDerived X) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj K.obj ⟶ K'.obj)
    (h_source : derivedQuasiCoherentModuleProperty X ((model.sourceRHom E).obj K.obj))
    (h_target : derivedQuasiCoherentModuleProperty X'
      ((model.targetRHom ((ModuleDerived.pullback g').obj E)).obj K'.obj)) :
    internalHomMap g' model E K K' α h_source h_target =
      Functor.PullbackInternalHom.comparisonOf model.sourceClosed model.targetClosed
          (ModuleDerived.pullback g')
          (fun A B ↦ (Functor.Monoidal.μIso (ModuleDerived.pullback g') A B).symm)
          E K.obj ≫ (model.targetRHom ((ModuleDerived.pullback g').obj E)).map α := by
  symm
  unfold DerivedInternalHomPullback.sourceClosed DerivedInternalHomPullback.targetClosed
  rw [Functor.PullbackInternalHom.comparisonOf, DerivedInternalHomPullback.closedOf_curry]
  rw [← (model.targetRHomAdjunction ((ModuleDerived.pullback g').obj E)).homEquiv_naturality_right]
  unfold internalHomMap
  congr 1
  unfold Functor.PullbackInternalHom.evaluationOf
  change ((model.targetModel.objIsoTensor
      ((ModuleDerived.pullback g').obj ((model.sourceRHom E).obj K.obj))
      ((ModuleDerived.pullback g').obj E)).hom ≫
    (Functor.Monoidal.μIso (ModuleDerived.pullback g') ((model.sourceRHom E).obj K.obj) E).hom ≫
    (ModuleDerived.pullback g').map ((β_ ((model.sourceRHom E).obj K.obj) E).hom ≫
      (MonoidalClosed.adjunctionOf
        (DerivedInternalHomPullback.closedOf model.sourceModel model.sourceRHom
          model.sourceRHomAdjunction) E).counit.app K.obj)) ≫ α = _
  rw [DerivedInternalHomPullback.closedOf_evaluation]
  simp only [Functor.map_comp, Category.assoc]

end DerivedTensorPullback

/-- Lemma 75.21.3 (2): on a cartesian square of algebraic spaces over a scheme `S`, if
`K` is in `D_QCoh(𝒪_X)` and `L(g')^* K ⟶ K'` satisfies the equivalent conditions of
Lemma 75.21.1, then for `E` perfect in `D(𝒪_X)` those conditions hold for
`L(g')^* RHom(E, K) ⟶ RHom(L(g')^* E, K')`. -/
@[stacks 0DKI]
theorem cohomologyBaseChange_internalHom_of_isPerfect {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [(ModuleDerived.pullback g').Monoidal]
    (sq : IsPullback g' f' f g)
    (model : DerivedInternalHomPullback g')
    (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (E : ModuleDerived X) (hE : ModuleDerived.IsPerfect E)
    (hα : cohomologyBaseChangeHolds sq K K' α) :
    cohomologyBaseChangeHolds sq
      (internalHomObj (model.sourceRHom E) K
        (model.sourceRHom_mem_of_isPerfect E K hE))
      (internalHomObj (model.targetRHom ((ModuleDerived.pullback g').obj E))
        K'
        (model.targetRHom_mem_of_isPerfect E K' hE))
      (DerivedTensorPullback.internalHomMap g' model E K K' α
        (model.sourceRHom_mem_of_isPerfect E K hE)
        (model.targetRHom_mem_of_isPerfect E K' hE)) := sorry

/-- Lemma 75.21.3 (3): on a cartesian square of algebraic spaces over a scheme `S`, if
`K` is bounded below in `D_QCoh(𝒪_X)` and `L(g')^* K ⟶ K'` satisfies the equivalent
conditions of Lemma 75.21.1, then for `E` pseudo-coherent in `D(𝒪_X)` those conditions
hold for `L(g')^* RHom(E, K) ⟶ RHom(L(g')^* E, K')`. -/
@[stacks 0DKI]
theorem cohomologyBaseChange_internalHom_of_isPseudoCoherent_of_boundedBelow
    {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [(ModuleDerived.pullback g').Monoidal]
    (sq : IsPullback g' f' f g)
    (model : DerivedInternalHomPullback g')
    (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (E : ModuleDerived X)
    (hK : (t.plus : ObjectProperty (ModuleDerived X)) K.obj)
    (hE : IsPseudoCoherent X E) (hα : cohomologyBaseChangeHolds sq K K' α) :
    cohomologyBaseChangeHolds sq
      (internalHomObj (model.sourceRHom E) K
        (model.sourceRHom_mem_of_isPseudoCoherent E K hE hK))
      (internalHomObj (model.targetRHom ((ModuleDerived.pullback g').obj E))
        K'
        (model.targetRHom_mem_of_isPseudoCoherent f' f g sq K K' α hα hK E hE))
      (DerivedTensorPullback.internalHomMap g' model E K K' α
        (model.sourceRHom_mem_of_isPseudoCoherent E K hE hK)
        (model.targetRHom_mem_of_isPseudoCoherent f' f g sq K K' α hα hK E hE)) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
