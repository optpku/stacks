/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Colimits
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.InternalHom
import StacksCheckRecall

/-!
# Quasi-coherent colimits, tensor products, and internal Hom

Quasi-coherent modules on a category fibred in groupoids have colimits agreeing
with the ambient Zariski, étale, fppf, and locally quasi-coherent categories.
Their tensor products agree across these topologies. Internal Hom from a finite
locally free module is represented by one quasi-coherent object and evaluation.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory CategoryTheory.Limits
open scoped SheafOfModules.RingedSite

universe u

/- Lemma 96.12.5 (1). Quasi-coherent modules have colimits agreeing with the
ambient module and locally quasi-coherent categories. -/
@[stacks 06WN] #check (AlgebraicGeometry.GroupoidsOver.QCoh.closedUnderColimitsOfShape :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (J : Type u) [Category.{u} J],
    (quasiCoherentModuleProperty X).IsClosedUnderColimitsOfShape J)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.inclusion_createsColimitsOfShape :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (J : Type u) [Category.{u} J],
    CreatesColimitsOfShape J (quasiCoherentModuleProperty X).ι)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.hasColimitsOfShape :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (J : Type u) [Category.{u} J],
    HasColimitsOfShape J (QCoh X))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.toAssociatedModules_preservesColimitsOfShape_zariski :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (J : Type u) [Category.{u} J],
    PreservesColimitsOfShape J (QCoh.toAssociatedModules X .zariski))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.toAssociatedModules_preservesColimitsOfShape_etale :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (J : Type u) [Category.{u} J],
    PreservesColimitsOfShape J (QCoh.toAssociatedModules X .etale))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.toAssociatedModules_preservesColimitsOfShape_fppf :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (J : Type u) [Category.{u} J],
    PreservesColimitsOfShape J (QCoh.toAssociatedModules X .fppf))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.toEtaleModules_preservesColimitsOfShape :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (J : Type u) [Category.{u} J],
    PreservesColimitsOfShape J (QCoh.toEtaleModules X))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.toLQCoh_preservesColimitsOfShape :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (J : Type u) [Category.{u} J],
    PreservesColimitsOfShape J (QCoh.toLQCoh X))

/- Lemma 96.12.5 (2). Tensor products agree in the Zariski, étale, and fppf
module categories and have a common quasi-coherent value. -/
@[stacks 06WN] #check (AlgebraicGeometry.GroupoidsOver.QCoh.quasicoherentTensor :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} (F G : QCoh X), QCoh X)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.quasicoherentTensor_obj :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} (F G : QCoh X),
    (QCoh.quasicoherentTensor F G).obj =
      (fromCommAssociatedModules X).obj
        (moduleTensorAssociated
          ((QCoh.toCommAssociatedModules X .fppf).obj F)
          ((QCoh.toCommAssociatedModules X .fppf).obj G)))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.tensorComparison_isIso_zariski :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} (F G : QCoh X),
    IsIso (QCoh.tensorComparison .zariski F G))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.tensorComparison_isIso_etale :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} (F G : QCoh X),
    IsIso (QCoh.tensorComparison .etale F G))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.tensorComparison_isIso_fppf :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} (F G : QCoh X),
    IsIso (QCoh.tensorComparison .fppf F G))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.finiteLocallyFree_tfae :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} (F : QCoh X),
    List.TFAE
      [SheafOfModules.IsFiniteLocallyFree F.obj,
        SheafOfModules.IsFiniteLocallyFree ((QCoh.toAssociatedModules X .zariski).obj F),
        SheafOfModules.IsFiniteLocallyFree ((QCoh.toAssociatedModules X .etale).obj F),
        SheafOfModules.IsFiniteLocallyFree ((QCoh.toAssociatedModules X .fppf).obj F)])

/- Lemma 96.12.5 (3). Quasi-coherent internal Hom from a finite locally free module
has one common object and evaluation in the Zariski, étale, and fppf topologies. -/
@[stacks 06WN] #check (AlgebraicGeometry.GroupoidsOver.QCoh.internalHom :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} (F G : QCoh X)
    [SheafOfModules.IsFiniteLocallyFree F.obj],
    ∃ (H : QCoh X) (ev : QCoh.quasicoherentTensor F H ⟶ G),
      ∀ τ ∈ [StandardTopology.zariski, .etale, .fppf],
        IsIso (QCoh.internalHomComparison τ F G H ev))
