/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.BigQuasicoherent.Colimits
import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.InternalHom.FiniteLocallyFree
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.AssociatedModule

variable (S : Scheme.{u}) (J : Type v) [Category.{w} J]

/- Lemma 35.10.6 (1): quasi-coherent modules on the big fppf site have
universe-compatible colimits. -/
@[stacks 0GNE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.BigQuasicoherent.hasColimitsOfShape
    S .fppf J :
      HasColimitsOfShape J
        (@SheafOfModules.isQuasicoherent (Over S) inferInstance
          (StandardTopology.fppf.overTopology S) (bigStructureSheaf .fppf S)
          (AlgebraicGeometry.StandardTopology.Big.over_hasWeakSheafify .fppf S)
          (AlgebraicGeometry.StandardTopology.Big.over_wEqualsLocallyBijective .fppf S)).FullSubcategory)

variable (σ : SmallStandardTopology)

/- Lemma 35.10.6 (2): these colimits agree with ambient colimits on the big
Zariski and big étale sites. -/
@[stacks 0GNE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.bigModuleFunctorPreservesColimits
    S σ.toStandard J :
      PreservesColimitsOfShape J (bigModuleFunctor S σ.toStandard))

/- Lemma 35.10.6 (3): these colimits agree with ambient colimits on the big
fppf site. -/
@[stacks 0GNE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.bigModuleFunctorPreservesColimits
    S .fppf J : PreservesColimitsOfShape J (bigModuleFunctor S .fppf))

variable (F G : Scheme.QCoh S)

/- Lemma 35.10.6 (4): the common quasi-coherent value of the tensor product. -/
@[stacks 0GNE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.quasicoherentTensor S F G :
    Scheme.QCoh S)

/- Lemma 35.10.6 (5): the big Zariski and big étale tensor comparisons are
invertible. -/
@[stacks 0GNE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.bigTensorComparisonIsIso
    S σ.toStandard F G :
      IsIso (bigModuleTensorComparison S σ.toStandard F G))

/- Lemma 35.10.6 (6): the big fppf tensor comparison is invertible. -/
@[stacks 0GNE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.bigTensorComparisonIsIso
    S .fppf F G : IsIso (bigModuleTensorComparison S .fppf F G))

/- Lemma 35.10.6 (7): finite local freeness agrees between the scheme and its
big Zariski or big étale associated module. -/
@[stacks 0GNE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.Property.big_iff
    AlgebraicGeometry.Scheme.AssociatedModule.Property.finiteLocallyFree
    σ.toStandard S F :
      F.obj.IsFiniteLocallyFree ↔
        ((bigFunctor σ.toStandard S).obj F).obj.IsFiniteLocallyFree)

/- Lemma 35.10.6 (8): finite local freeness agrees between the scheme and its
big fppf associated module. -/
@[stacks 0GNE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.Property.big_iff
    AlgebraicGeometry.Scheme.AssociatedModule.Property.finiteLocallyFree
    .fppf S F :
      AlgebraicGeometry.Scheme.AssociatedModule.Property.finiteLocallyFree.scheme F ↔
        AlgebraicGeometry.Scheme.AssociatedModule.Property.finiteLocallyFree.big .fppf S F)

variable [F.obj.IsFiniteLocallyFree]

/- Lemma 35.10.6 (9): the common quasi-coherent value of internal Hom from a
finite locally free source. -/
@[stacks 0GNE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.quasicoherentInternalHom S F G
    (SheafOfModules.IsFiniteLocallyFree.isFinitePresentation F.obj) : Scheme.QCoh S)

/- Lemma 35.10.6 (10): the big Zariski and big étale internal-Hom comparisons
from a finite locally free source are invertible. -/
@[stacks 0GNE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.bigModuleInternalHomComparisonIsIsoOfFiniteLocallyFree
    S σ.toStandard F G :
      IsIso (bigModuleInternalHomComparison S σ.toStandard F G
        (SheafOfModules.IsFiniteLocallyFree.isFinitePresentation F.obj)))

/- Lemma 35.10.6 (11): the big fppf internal-Hom comparison from a finite
locally free source is invertible. -/
@[stacks 0GNE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.bigModuleInternalHomComparisonIsIsoOfFiniteLocallyFree
    S .fppf F G :
      IsIso (bigModuleInternalHomComparison S .fppf F G
        (SheafOfModules.IsFiniteLocallyFree.isFinitePresentation F.obj)))

end AlgebraicGeometry.Scheme.AssociatedModule
