/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift.Ideal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.PowerQuotient.Module
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact

/-!
# Internal Hom of coherent completions on algebraic spaces

The ideal-power quotients of the internal-Hom sheaf form an inverse system of
global sections. Evaluation of a compatible family at every quotient stage
gives a comparison from its inverse limit to morphisms of completed coherent
modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.IdealSheaf
open SheafOfModules.RingedSite.InternalHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoherentCompletion

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The ideal-power quotient `Hom(F, G) / I ^ n Hom(F, G)` on the universe-lifted
commutative presentation. -/
noncomputable abbrev homStage [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X) (n : ℕ) :
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X) :=
  PowerQuotientModule.stage.{u + 1, u, u + 1} (liftedIdealSubobject I)
    (internalHom F.obj G.obj) n

/-- The inverse system whose stage `n` consists of global sections of
`Hom(F, G) / I ^ n Hom(F, G)`. -/
noncomputable def homSectionsSystem [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X) : ℕᵒᵖ ⥤ Type (u + 1) :=
  PowerQuotientModule.sectionsSystem.{u + 1, u, u + 1} (liftedIdealSubobject I)
    (internalHom F.obj G.obj)

/-- Stage `n` of the internal-Hom sections system is the type of global sections
of `Hom(F, G) / I ^ n Hom(F, G)`. -/
theorem homSectionsSystem_obj [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X) (n : ℕ) :
    (homSectionsSystem I F G).obj (op n) = (homStage I F G n).sections := rfl

/-- The section represented by a compatible family in the inverse limit at
stage `n`. -/
noncomputable def homSection [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X)
    (x : limit (homSectionsSystem I F G)) (n : ℕ) :
    (homStage I F G n).sections :=
  limit.π (homSectionsSystem I F G) (op n) x

/-- The curried evaluation map from `Hom(F, G) / I ^ n Hom(F, G)` to
`Hom(F, G / I ^ n G)`. -/
noncomputable def homReduce [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X) (n : ℕ) :
    homStage I F G n ⟶ internalHom F.obj (idealPowerQuotient I G.obj n) :=
  homEquiv (commStructureSheafLift X) (liftModule F.obj) (homStage I F G n)
    (liftModule (idealPowerQuotient I G.obj n))
    ((PreservesCokernel.iso (tensorLeft (liftModule F.obj))
        (powerAction (liftedIdealSubobject I) (internalHom F.obj G.obj) n)).hom ≫
      cokernel.desc
        ((tensorLeft (liftModule F.obj)).map
          (powerAction (liftedIdealSubobject I) (internalHom F.obj G.obj) n))
        ((homEquiv (commStructureSheafLift X) (liftModule F.obj)
            (internalHom F.obj G.obj) (liftModule G.obj)).symm
            (𝟙 (internalHom F.obj G.obj)) ≫
          liftModuleMap (idealPowerQuotient.projection I G.obj n))
        (by sorry))

/-- Evaluation of a compatible internal-Hom section on the stage-`n` ideal-power
quotients, as a morphism of underlying modules. -/
noncomputable def homQuotientMap [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X)
    (x : limit (homSectionsSystem I F G)) (n : ℕ) :
    idealPowerQuotient I F.obj n ⟶ idealPowerQuotient I G.obj n :=
  cokernel.desc (idealPowerProductSubobject I F.obj n).arrow
    (unliftModuleHom
      (sectionsHomEquiv (commStructureSheafLift X) (liftModule F.obj)
        (liftModule (idealPowerQuotient I G.obj n))
        (SheafOfModules.sectionsMap (homReduce I F G n) (homSection I F G x n))))
    (by sorry)

/-- The map on coherent completion stages obtained by evaluating a compatible
internal-Hom family. -/
noncomputable def homComparisonStageMap [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X)
    (x : limit (homSectionsSystem I F G)) (n : ℕ) :
    stage I F n ⟶ stage I G n :=
  ObjectProperty.homMk (homQuotientMap I F G x n)

/-- The stage maps defined by a compatible family commute with completion
transitions. -/
theorem homComparisonStageMap_naturality [IsNoetherian X]
    (I : IdealSubobject X) [IsQuasiCoherent I] (F G : Coh X)
    (x : limit (homSectionsSystem I F G)) (n : ℕ) :
    (system I F).map (homOfLE (Nat.le_add_right n 1)).op ≫
        homComparisonStageMap I F G x n =
      homComparisonStageMap I F G x (n + 1) ≫
        (system I G).map (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- A compatible family of internal-Hom quotient sections determines a morphism
between the corresponding coherent formal completions. -/
noncomputable def homComparison [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X) :
    limit (homSectionsSystem I F G) → (obj I F ⟶ obj I G) :=
  fun x ↦ ObjectProperty.homMk
    (NatTrans.ofOpSequence (homComparisonStageMap I F G x)
      (homComparisonStageMap_naturality I F G x))

/-- Evaluating the underlying natural transformation of the Hom comparison at
stage `n` recovers the stage morphism associated to the compatible family. -/
theorem homComparison_apply [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X)
    (x : limit (homSectionsSystem I F G)) (n : ℕ) :
    (homComparison I F G x).hom.app (op n) =
      homComparisonStageMap I F G x n := rfl

/-- The canonical comparison from the inverse limit of internal-Hom quotient
sections to morphisms between coherent formal completions is bijective. -/
theorem homComparison_bijective [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F G : Coh X) :
    Function.Bijective (homComparison I F G) := sorry

end AlgebraicGeometry.AlgebraicSpace.CoherentCompletion
