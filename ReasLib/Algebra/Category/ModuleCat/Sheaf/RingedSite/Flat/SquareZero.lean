module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.CategoryTheory.Monoidal.SquareZero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness and square-zero reductions of module sheaves

A square-zero reduction consists of two short exact sequences: the square-zero kernel sequence of
structure sheaves and the quotient presentation of the module.  Packaging the exactness at the
`ShortComplex.ShortExact` level removes the asymmetric collection of separate mono, exact, and epi
fields and gives downstream code the standard homological API immediately.
-/

@[expose] public section

open CategoryTheory
open scoped MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O' O : Sheaf J CommRingCat.{max u v}}

namespace SquareZeroReduction

/-- The kernel sequence `I ⟶ O' ⟶ O` associated to a same-site reduction. -/
noncomputable def idealSequence (alpha : O' ⟶ O)
    (I : ringedSiteModuleCategory J O')
    (i : I ⟶ unitModule J O')
    (h : i ≫ SheafOfModules.unitToPushforwardObjUnit
      (ringedSiteStructureMap alpha) = 0) :
    ShortComplex (ringedSiteModuleCategory J O') :=
  ShortComplex.mk i
    (SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap alpha)) h

/-- The module sequence `I ⊗ F ⟶ F' ⟶ F` associated to a square-zero reduction. -/
noncomputable def quotientSequence (alpha : O' ⟶ O)
    (I F' : ringedSiteModuleCategory J O')
    (F : ringedSiteModuleCategory J O)
    (tensorTo : moduleTensor I ((restrictionAlong alpha).obj F) ⟶ F')
    (quot : F' ⟶ (restrictionAlong alpha).obj F)
    (h : tensorTo ≫ quot = 0) :
    ShortComplex (ringedSiteModuleCategory J O') :=
  ShortComplex.mk tensorTo quot h

end SquareZeroReduction

/-- A square-zero reduction of a module is a square-zero short exact kernel sequence together with
the short exact quotient sequence `I ⊗ F ⟶ F' ⟶ F`. -/
@[stacks 08M4 "reduction data"]
class IsSquareZeroReduction
    (alpha : O' ⟶ O)
    (I : ringedSiteModuleCategory J O')
    (i : I ⟶ unitModule J O')
    (F' : ringedSiteModuleCategory J O')
    (F : ringedSiteModuleCategory J O)
    (tensorTo : moduleTensor I ((restrictionAlong alpha).obj F) ⟶ F')
    (quot : F' ⟶ (restrictionAlong alpha).obj F) : Prop where
  /-- The ideal inclusion followed by the structure map is zero. -/
  ideal_comp :
    i ≫ SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap alpha) = 0
  /-- The kernel sequence `I ⟶ O' ⟶ O` is short exact. -/
  ideal_shortExact :
    (SquareZeroReduction.idealSequence alpha I i ideal_comp).ShortExact
  /-- The ideal inclusion, transported to the tensor unit, is square-zero. -/
  square_zero :
    CategoryTheory.MonoidalCategory.IsSquareZero (i ≫ unitIsoTensorUnit.hom)
  /-- The tensor-action map followed by the quotient map is zero. -/
  quotient_comp : tensorTo ≫ quot = 0
  /-- The module reduction sequence `I ⊗ F ⟶ F' ⟶ F` is short exact. -/
  quotient_shortExact :
    (SquareZeroReduction.quotientSequence alpha I F' F tensorTo quot quotient_comp).ShortExact

namespace IsSquareZeroReduction

variable {alpha : O' ⟶ O}
variable {I : ringedSiteModuleCategory J O'} {i : I ⟶ unitModule J O'}
variable {F' : ringedSiteModuleCategory J O'} {F : ringedSiteModuleCategory J O}
variable {tensorTo : moduleTensor I ((restrictionAlong alpha).obj F) ⟶ F'}
variable {quot : F' ⟶ (restrictionAlong alpha).obj F}

/-- The ideal inclusion in a square-zero reduction is a monomorphism. -/
theorem idealInclusion_mono
    (h : IsSquareZeroReduction alpha I i F' F tensorTo quot) : Mono i := sorry

/-- The structure-map quotient in a square-zero reduction is an epimorphism. -/
theorem structureMap_epi
    (h : IsSquareZeroReduction alpha I i F' F tensorTo quot) :
    Epi (SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap alpha)) := sorry

/-- The module quotient map in a square-zero reduction is an epimorphism. -/
theorem quotient_epi
    (h : IsSquareZeroReduction alpha I i F' F tensorTo quot) : Epi quot := sorry

/-- The ideal part of a square-zero reduction consists simultaneously of a short exact kernel
sequence and the sectionwise square-zero condition. -/
theorem ideal_spec [h : IsSquareZeroReduction alpha I i F' F tensorTo quot] :
    (SquareZeroReduction.idealSequence alpha I i h.ideal_comp).ShortExact ∧
      CategoryTheory.MonoidalCategory.IsSquareZero
        (i ≫ unitIsoTensorUnit.hom) := sorry

/-- The quotient part of a square-zero reduction is the canonical short exact module sequence. -/
theorem quotient_spec [h : IsSquareZeroReduction alpha I i F' F tensorTo quot] :
    (SquareZeroReduction.quotientSequence
      alpha I F' F tensorTo quot h.quotient_comp).ShortExact := sorry

/-- Lemma 18.28.15 (08M4): a module over a square-zero thickening is flat exactly when its
reduction is flat and the kernel-action map is monic. -/
@[stacks 08M4]
theorem isFlat_iff [IsSquareZeroReduction alpha I i F' F tensorTo quot] :
    IsFlat O' F' ↔ IsFlat O F ∧ Mono tensorTo := sorry

end IsSquareZeroReduction

end SheafOfModules.RingedSite
