/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor.Bifunctor
public import ReasLib.CategoryTheory.Functor.Derived.TensorComparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Counit compatibility for derived pullback and tensor

The comparison between derived pullback of a derived tensor product and the derived tensor
product of the two pullbacks is formal at the level of total left-derived bifunctors.  This file
specializes that construction to module sheaves and names the six arrows in its counit diagram.
The resulting commutative square is the reusable formal content of Stacks Project, Lemma 21.18.8.
-/

@[expose] public section

-- This is the standard quotient used by the named ringed-site models.
-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard

-- Keep these operations on the already specified canonical derived-category model.
-- Local instance justification (defeq pin): ModuleDerived and DerivedCategory.Q must elaborate to the same bundled-ringed-site standard localization; enable the existing reducible moduleCat_hasDerivedCategory owner only for these module comparisons.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open CategoryTheory.Functor.LeftDerived

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom.modulePullbackDerived.TensorPreservation.Counit

variable {CX : Type uX} [Category.{vX} CX]
variable {CY : Type uY} [Category.{vY} CY]
variable {JX : GrothendieckTopology CX} {JY : GrothendieckTopology CY}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify JX AddCommGrpCat.{w}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JY AddCommGrpCat.{w}]
variable [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}

variable (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
  (RingedSite.ofCommRingSheaf JY OY))
variable [(f.modulePushforward.{w}).IsRightAdjoint]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{w} f)
  (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY))]
variable [Functor.Monoidal f.modulePullback.{w}]
variable [ModuleDerived.KFlat.HomotopyTensorDescends (J := JX) OX]
variable [ModuleDerived.KFlat.HomotopyTensorDescends (J := JY) OY]
variable [Functor.Homotopy.Cochain.TensorComparison.IsInvertible f.modulePullback.{w}]
variable [ModuleDerived.Tensor.Has (J := JX) OX]
variable [ModuleDerived.Tensor.Has (J := JY) OY]

/-- The total-left-derived pullback counit from localized derived pullback to ordinary
homotopy pullback followed by localization. -/
@[stacks 0FPH "derived pullback counit"]
noncomputable abbrev pullbackCounit :
    moduleLocalization.{w} (RingedSite.ofCommRingSheaf JY OY) ⋙
        modulePullbackDerived.{w} f ⟶
      modulePullbackHomotopy.{w} f ⋙
        moduleLocalization.{w} (RingedSite.ofCommRingSheaf JX OX) :=
  (modulePullbackToDerived.{w} f).totalLeftDerivedCounit
    (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JY OY))
    (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY))

/-- The underived tensorator of homotopy pullback, in the lax monoidal direction. -/
@[stacks 0FPH "homotopy pullback tensorator"]
noncomputable abbrev homotopyTensorator :
    (modulePullbackHomotopy.{w} f).prod (modulePullbackHomotopy.{w} f) ⋙
        MonoidalCategory.tensor
          (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JX OX)) ≅
      MonoidalCategory.tensor
          (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY OY)) ⋙
        modulePullbackHomotopy.{w} f :=
  Functor.Monoidal.μNatIso (modulePullbackHomotopy.{w} f)

/-- The canonical presentation isomorphism from tensoring homotopy objects and then localizing to
the uncurried source presentation used by the derived tensor bifunctor. -/
@[stacks 0FPH "localized tensor source presentation"]
noncomputable abbrev sourcePresentationIso (O : Sheaf JY CommRingCat.{w}) :
    MonoidalCategory.tensor
        (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY O)) ⋙
        moduleLocalization.{w} (RingedSite.ofCommRingSheaf JY O) ≅
      ModuleDerived.Tensor.sourceFunctor O :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.sourceFunctorIso

/-- The derived tensor counit in the explicit tensor-then-localize presentation required by the
tensor-comparison API. -/
@[stacks 0FPH "derived tensor counit in tensor source presentation"]
noncomputable abbrev tensorCounit (O : Sheaf JY CommRingCat.{w})
    [ModuleDerived.Tensor.Has (J := JY) O] :
    (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JY O)).prod
        (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JY O)) ⋙
        ModuleDerived.Tensor.functor O ⟶
      MonoidalCategory.tensor
          (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY O)) ⋙
        moduleLocalization.{w} (RingedSite.ofCommRingSheaf JY O) :=
  ModuleDerived.Tensor.counit O ≫ (sourcePresentationIso O).inv

/-- Tensor first on the source homotopy category, then pull back and localize. -/
@[stacks 0FPH "tensor-then-pullback raw functor"]
abbrev sourceRaw :
    (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY OY) ×
        ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY OY)) ⥤
      ModuleDerived.{w} (RingedSite.ofCommRingSheaf JX OX) :=
  TensorComparison.sourceRaw
    (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JX OX))
    (modulePullbackHomotopy.{w} f)
    (MonoidalCategory.tensor
      (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY OY)))

/-- Pull back in both variables, tensor on the target homotopy category, and localize. -/
@[stacks 0FPH "pullback-then-tensor raw functor"]
abbrev targetRaw :
    (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY OY) ×
        ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY OY)) ⥤
      ModuleDerived.{w} (RingedSite.ofCommRingSheaf JX OX) :=
  TensorComparison.targetRaw
    (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JX OX))
    (modulePullbackHomotopy.{w} f)
    (MonoidalCategory.tensor
      (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JX OX)))

/-- Existence of the direct total left-derived model for tensor followed by pullback. -/
@[stacks 0FPH "tensor-then-pullback direct derived existence"]
abbrev SourceHasLeftDerived : Prop :=
  (sourceRaw (JX := JX) (JY := JY) f).HasLeftDerivedFunctor
    (ModuleDerived.Tensor.qis (J := JY) OY)

/-- Existence of the direct total left-derived model for pullback followed by tensor. -/
@[stacks 0FPH "pullback-then-tensor direct derived existence"]
abbrev TargetHasLeftDerived : Prop :=
  (targetRaw (JX := JX) (JY := JY) f).HasLeftDerivedFunctor
    (ModuleDerived.Tensor.qis (J := JY) OY)

/-- The localized raw tensor isomorphism used before total left derivation. -/
@[stacks 0FPH "localized raw pullback tensor comparison"]
noncomputable abbrev rawComparisonIso :
    targetRaw (JX := JX) (JY := JY) f ≅
      sourceRaw (JX := JX) (JY := JY) f :=
  TensorComparison.rawComparisonIso
    (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JX OX))
    (modulePullbackHomotopy.{w} f)
    (MonoidalCategory.tensor
      (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY OY)))
    (MonoidalCategory.tensor
      (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JX OX)))
    (homotopyTensorator f)

/-- The iterated counit for derived tensor followed by derived pullback. -/
@[stacks 0FPH "tensor-then-pullback counit"]
noncomputable abbrev sourceCounit :
    ModuleDerived.Tensor.localization (J := JY) OY ⋙
        (ModuleDerived.Tensor.functor (J := JY) OY ⋙
          modulePullbackDerived.{w} f) ⟶
      sourceRaw (JX := JX) (JY := JY) f :=
  TensorComparison.sourceCounit
    (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JY OY))
    (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JX OX))
    (modulePullbackHomotopy.{w} f) (modulePullbackDerived.{w} f)
    (MonoidalCategory.tensor
      (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY OY)))
    (ModuleDerived.Tensor.functor (J := JY) OY)
    (pullbackCounit f) (tensorCounit (JY := JY) OY)

/-- The iterated counit for derived pullback in both variables followed by derived tensor. -/
@[stacks 0FPH "pullback-then-tensor counit"]
noncomputable abbrev targetCounit :
    ModuleDerived.Tensor.localization (J := JY) OY ⋙
        ((modulePullbackDerived.{w} f).prod (modulePullbackDerived.{w} f) ⋙
          ModuleDerived.Tensor.functor (J := JX) OX) ⟶
      targetRaw (JX := JX) (JY := JY) f :=
  TensorComparison.targetCounit
    (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JY OY))
    (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JX OX))
    (modulePullbackHomotopy.{w} f) (modulePullbackDerived.{w} f)
    (MonoidalCategory.tensor
      (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JX OX)))
    (ModuleDerived.Tensor.functor (J := JX) OX)
    (pullbackCounit f) (tensorCounit (JY := JX) OX)

/-- The condition that tensor followed by derived pullback is a left-derived model of the raw
tensor-then-pullback functor. -/
@[stacks 0FPH "tensor-then-pullback left-derived model"]
abbrev SourceIsLeftDerived : Prop :=
  Functor.IsLeftDerivedFunctor
    (ModuleDerived.Tensor.functor (J := JY) OY ⋙ modulePullbackDerived.{w} f)
    (sourceCounit f) (ModuleDerived.Tensor.qis (J := JY) OY)

/-- The condition that derived pullback in both variables followed by tensor is a left-derived
model of the raw pullback-then-tensor functor. -/
@[stacks 0FPH "pullback-then-tensor left-derived model"]
abbrev TargetIsLeftDerived : Prop :=
  Functor.IsLeftDerivedFunctor
    ((modulePullbackDerived.{w} f).prod (modulePullbackDerived.{w} f) ⋙
      ModuleDerived.Tensor.functor (J := JX) OX)
    (targetCounit f) (ModuleDerived.Tensor.qis (J := JY) OY)

section DirectModels

variable [SourceHasLeftDerived (JX := JX) (JY := JY) f]
variable [TargetHasLeftDerived (JX := JX) (JY := JY) f]

/-- Comparison from the iterated tensor-then-pullback model to its direct total left-derived
model. -/
@[stacks 0FPH "tensor-then-pullback derived comparison"]
noncomputable abbrev sourceComparison :
    ModuleDerived.Tensor.functor (J := JY) OY ⋙
        modulePullbackDerived.{w} f ⟶
      TensorComparison.sourceDerived
        (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JY OY))
        (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JX OX))
        (modulePullbackHomotopy.{w} f)
        (MonoidalCategory.tensor
          (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY OY)))
        (ModuleDerived.Tensor.qis (J := JY) OY) :=
  TensorComparison.sourceComparison
    (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JY OY))
    (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JX OX))
    (modulePullbackHomotopy.{w} f) (modulePullbackDerived.{w} f)
    (MonoidalCategory.tensor
      (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY OY)))
    (ModuleDerived.Tensor.functor (J := JY) OY)
    (ModuleDerived.Tensor.qis (J := JY) OY)
    (pullbackCounit f) (tensorCounit (JY := JY) OY)

/-- Comparison from the iterated pullback-then-derived-tensor model to its direct total
left-derived model. -/
@[stacks 0FPH "pullback-then-tensor derived comparison"]
noncomputable abbrev targetComparison :
    (modulePullbackDerived.{w} f).prod (modulePullbackDerived.{w} f) ⋙
        ModuleDerived.Tensor.functor (J := JX) OX ⟶
      TensorComparison.targetDerived
        (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JY OY))
        (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JX OX))
        (modulePullbackHomotopy.{w} f)
        (MonoidalCategory.tensor
          (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JX OX)))
        (ModuleDerived.Tensor.qis (J := JY) OY) :=
  TensorComparison.targetComparison
    (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JY OY))
    (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JX OX))
    (modulePullbackHomotopy.{w} f) (modulePullbackDerived.{w} f)
    (MonoidalCategory.tensor
      (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JX OX)))
    (ModuleDerived.Tensor.functor (J := JX) OX)
    (ModuleDerived.Tensor.qis (J := JY) OY)
    (pullbackCounit f) (tensorCounit (JY := JX) OX)

end DirectModels

variable [TargetIsLeftDerived (JX := JX) (JY := JY) f]

/-- The canonical comparison from pullback of the two-variable derived tensor to derived tensor
of the two pullbacks. -/
@[stacks 0FPH "biderived pullback tensor comparison"]
noncomputable abbrev comparison :
    ModuleDerived.Tensor.functor (J := JY) OY ⋙ modulePullbackDerived.{w} f ⟶
      (modulePullbackDerived.{w} f).prod (modulePullbackDerived.{w} f) ⋙
        ModuleDerived.Tensor.functor (J := JX) OX :=
  TensorComparison.comparison
    (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JY OY))
    (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JX OX))
    (modulePullbackHomotopy.{w} f) (modulePullbackDerived.{w} f)
    (MonoidalCategory.tensor
      (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY OY)))
    (MonoidalCategory.tensor
      (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JX OX)))
    (ModuleDerived.Tensor.functor (J := JY) OY)
    (ModuleDerived.Tensor.functor (J := JX) OX)
    (ModuleDerived.Tensor.qis (J := JY) OY) (pullbackCounit f)
    (tensorCounit (JY := JY) OY)
    (tensorCounit (JY := JX) OX)
    (homotopyTensorator f)

/-- If the source iterated model also satisfies the left-derived universal property, then the
biderived pullback tensor comparison is invertible. -/
@[stacks 0FPH "biderived pullback tensor comparison is invertible"]
theorem comparison_isIso
    [SourceIsLeftDerived (JX := JX) (JY := JY) f] :
    IsIso (comparison (JX := JX) (JY := JY) f) := sorry

variable (K M : ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY OY))

/-- The top arrow: apply derived pullback to the derived-tensor counit. -/
@[stacks 0FPH "derived tensor counit after derived pullback"]
noncomputable abbrev top :=
  (modulePullbackDerived.{w} f).map
    ((tensorCounit (JY := JY) OY).app (K, M))

/-- The upper-left arrow: the bifunctorial derived pullback tensor comparison. -/
@[stacks 0FPH "upper derived pullback tensor comparison"]
noncomputable abbrev upperLeft :=
  (comparison f).app
    ((ModuleDerived.Tensor.localization (J := JY) OY).obj (K, M))

/-- The upper-right arrow: the derived pullback counit on the underived tensor product. -/
@[stacks 0FPH "pullback counit on tensor"]
noncomputable abbrev upperRight :=
  (pullbackCounit f).app
    ((MonoidalCategory.tensor
      (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY OY))).obj (K, M))

/-- The lower-left arrow: derived tensor applied to the two pullback counits. -/
@[stacks 0FPH "derived tensor of pullback counits"]
noncomputable abbrev lowerLeft :=
  (ModuleDerived.Tensor.functor (J := JX) OX).map
    (Prod.mkHom ((pullbackCounit f).app K) ((pullbackCounit f).app M))

/-- The lower-right arrow: the inverse localized underived pullback tensorator. -/
@[stacks 0FPH "inverse localized pullback tensorator"]
noncomputable abbrev lowerRight :=
  (rawComparisonIso (JX := JX) (JY := JY) f).inv.app (K, M)

/-- The bottom arrow: the target derived-tensor counit after ordinary pullback in both
variables. -/
@[stacks 0FPH "target derived tensor counit"]
noncomputable abbrev bottom :=
  (tensorCounit (JY := JX) OX).app
    ((modulePullbackHomotopy.{w} f).obj K, (modulePullbackHomotopy.{w} f).obj M)

/-- Lemma 21.18.8 (0FPH): the six canonical counit and tensor-comparison arrows form a
commutative diagram. -/
@[stacks 0FPH "derived pullback tensor counit diagram"]
theorem commSq :
    CommSq (top f K M) (upperLeft f K M ≫ lowerLeft f K M)
      (upperRight f K M ≫ lowerRight f K M) (bottom f K M) := sorry

section MonoidalModel

variable [ModuleDerived.KFlat.TensorDescends (J := JX) OX]
variable [ModuleDerived.KFlat.TensorDescends (J := JY) OY]
variable [ModuleDerived.KFlat.IsLocalization (J := JX) OX]
variable [ModuleDerived.KFlat.IsLocalization (J := JY) OY]
variable [ModuleDerived.KFlat.TermwiseFlat.IsLocalization (J := JY) OY]
variable [IsIso (GoodModels.comparison f)]

/-- Transport the 07A4 monoidal tensorator along chosen identifications of the total-left-derived
tensor bifunctors with the K-flat monoidal tensor bifunctors. -/
@[stacks 0FPH "transported 07A4 tensor comparison"]
noncomputable def monoidalComparison
    (eX : ModuleDerived.Tensor.functor (J := JX) OX ≅
      MonoidalCategory.tensor
        (ModuleDerived.{w} (RingedSite.ofCommRingSheaf JX OX)))
    (eY : ModuleDerived.Tensor.functor (J := JY) OY ≅
      MonoidalCategory.tensor
        (ModuleDerived.{w} (RingedSite.ofCommRingSheaf JY OY))) :
    ModuleDerived.Tensor.functor (J := JY) OY ⋙ modulePullbackDerived.{w} f ⟶
      (modulePullbackDerived.{w} f).prod (modulePullbackDerived.{w} f) ⋙
        ModuleDerived.Tensor.functor (J := JX) OX :=
  Functor.whiskerRight eY.hom (modulePullbackDerived.{w} f) ≫
    (RingedSite.Hom.modulePullbackDerived.TensorPreservation.natIso f).hom ≫
    Functor.whiskerLeft
      ((modulePullbackDerived.{w} f).prod (modulePullbackDerived.{w} f)) eX.inv

/-- The transported 07A4 tensorator is compatible with the two iterated counits when it satisfies
the model-independent left-derived tensor-comparison specification.  This condition rules out
changing either model identification by an unrelated automorphism. -/
@[stacks 0FPH "07A4 tensor comparison counit compatibility"]
abbrev IsMonoidalComparison
    (eX : ModuleDerived.Tensor.functor (J := JX) OX ≅
      MonoidalCategory.tensor
        (ModuleDerived.{w} (RingedSite.ofCommRingSheaf JX OX)))
    (eY : ModuleDerived.Tensor.functor (J := JY) OY ≅
      MonoidalCategory.tensor
        (ModuleDerived.{w} (RingedSite.ofCommRingSheaf JY OY))) : Prop :=
  TensorComparison.IsComparison
    (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JY OY))
    (moduleLocalization.{w} (RingedSite.ofCommRingSheaf JX OX))
    (modulePullbackHomotopy.{w} f) (modulePullbackDerived.{w} f)
    (MonoidalCategory.tensor
      (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JY OY)))
    (MonoidalCategory.tensor
      (ModuleHomotopy.{w} (RingedSite.ofCommRingSheaf JX OX)))
    (ModuleDerived.Tensor.functor (J := JY) OY)
    (ModuleDerived.Tensor.functor (J := JX) OX)
    (pullbackCounit f) (tensorCounit (JY := JY) OY)
    (tensorCounit (JY := JX) OX) (homotopyTensorator f)
    (monoidalComparison f eX eY)

/-- Under counit-compatible model isomorphisms from total-left-derived tensor to the K-flat
monoidal tensor, the formal biderived comparison is the transport of the 07A4 tensorator. -/
@[stacks 0FPH "compatibility with the 07A4 tensorator"]
theorem comparison_eq_monoidal
    (eX : ModuleDerived.Tensor.functor (J := JX) OX ≅
      MonoidalCategory.tensor
        (ModuleDerived.{w} (RingedSite.ofCommRingSheaf JX OX)))
    (eY : ModuleDerived.Tensor.functor (J := JY) OY ≅
      MonoidalCategory.tensor
        (ModuleDerived.{w} (RingedSite.ofCommRingSheaf JY OY)))
    (hcompat : IsMonoidalComparison (JX := JX) (JY := JY) f eX eY) :
    comparison (JX := JX) (JY := JY) f =
      monoidalComparison (JX := JX) (JY := JY) f eX eY := sorry

end MonoidalModel

-- The residual `sorryAx` in the site-specialized data comes from inherited module-sheaf and
-- homotopy-category law fields; no theorem asserting invertibility is installed as an instance.

end RingedSite.Hom.modulePullbackDerived.TensorPreservation.Counit
