/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra.Functor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Bimod.Equivalence
public import ReasLib.CategoryTheory.Monoidal.Bimod.Adjunction
public import ReasLib.CategoryTheory.Monoidal.Bimod.ChangeOfScalars.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lower shriek for differential graded modules

A monoidal right adjoint on cochain complexes restricts differential graded algebras and modules.
When its left adjoint satisfies the projection formula, the ambient adjunction lifts to right DG
modules.  The only normalization needed is the canonical isomorphism between the monoid associated
to the restricted DGA and the monoidal image of the original monoid.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule
open scoped SheafOfModules.RingedSite.LeftDifferentialGradedModule

noncomputable section

universe uC vC wC uD vD wD

namespace SheafOfModules.RingedSite.DifferentialGradedModule.LowerShriek

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
variable [HasWeakSheafify JC AddCommGrpCat.{wC}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{wC}]
variable [HasWeakSheafify JD AddCommGrpCat.{wD}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{wD}]
variable [UnivLE.{max uC vC, wC}] [UnivLE.{max uD vD, wD}]
variable {OC : Sheaf JC CommRingCat.{wC}} {OD : Sheaf JD CommRingCat.{wD}}

variable {L : CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := JC) (𝒪 := OC)) ℤ ⥤
  CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := JD) (𝒪 := OD)) ℤ}
variable {R : CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := JD) (𝒪 := OD)) ℤ ⥤
  CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := JC) (𝒪 := OC)) ℤ}
variable (adj : L ⊣ R)
variable [R.LaxMonoidal] [L.OplaxMonoidal] [adj.IsMonoidal]
variable [adj.ProjectionFormulaMap]

/-- The differential graded algebra obtained by applying the monoidal right adjoint to the
coefficient algebra. -/
@[stacks 0FRV "restricted differential graded algebra"]
noncomputable def restrictedAlgebra (A : DGA(OD)) : DGA(OC) :=
  (DifferentialGradedAlgebra.map
    (C := D) (D := C) (JC := JD) (JD := JC) (OC := OD) (OD := OC) R).obj A

-- Local declaration justification (search instability): fix both endpoints of the contravariant
-- functor while elaborating the dependent public signatures below; this notation installs no data.
local notation "RAlg(" A ")" => restrictedAlgebra
  (C := C) (D := D) (JC := JC) (JD := JD) (OC := OC) (OD := OD) (R := R) A

/-- The canonical comparison from the monoid underlying the restricted DGA to the monoidal image
of the original coefficient monoid. -/
@[stacks 0FRV "restricted coefficient monoid comparison"]
noncomputable def coefficientIso (A : DGA(OD)) :
    (RAlg(A)).toMon ≅ R.mapMon.obj A.toMon :=
  DifferentialGradedAlgebra.toMonCounitIso (𝒪 := OC) (R.mapMon.obj A.toMon)

-- Local declaration justification (search instability): reuse the endpoint-pinned comparison
-- above without exposing repeated site parameters in every downstream declaration.
local notation "RAlgIso(" A ")" => coefficientIso
  (C := C) (D := D) (JC := JC) (JD := JD) (OC := OC) (OD := OD) (R := R) A

/-- Convert a module over the restricted DGA to the canonically isomorphic monoid presentation
expected by monoidal module lower shriek.  This functor leaves its carrier unchanged. -/
@[stacks 0FRV "normalization of a restricted DG module"]
noncomputable def normalize (A : DGA(OD)) :
    Mod(RAlg(A), d) ⥤
      CategoryTheory.Bimod.RightModule (R.mapMon.obj A.toMon) :=
  toBimodFunctor (RAlg(A)) ⋙
    CategoryTheory.Bimod.restrictRightIso (RAlgIso(A))

/-- Restriction of right DG modules along a monoidal functor, including the canonical coefficient
normalization back to the homogeneous DGA presentation. -/
@[stacks 0FRW "restriction of right differential graded modules"]
noncomputable def restriction (A : DGA(OD)) :
    Mod(A, d) ⥤ Mod(RAlg(A), d) :=
  toBimodFunctor A ⋙ R.mapRightModule A.toMon ⋙
    CategoryTheory.Bimod.restrictRightIsoInverse (RAlgIso(A)) ⋙
    ofBimodFunctor (RAlg(A))

/-- Restriction of left DG modules along a monoidal functor.  The functor first normalizes the
tensor-unit action and then transports the coefficient action across `coefficientIso`. -/
@[stacks 0FRX "restriction of left differential graded modules"]
noncomputable def restrictionLeft (A : DGA(OD)) :
    DifferentialGradedAlgebra.LeftModule (J := JD) (𝒪 := OD) A ⥤
      DifferentialGradedAlgebra.LeftModule (J := JC) (𝒪 := OC) (RAlg(A)) :=
  R.mapLeftModule A.toMon ⋙
    CategoryTheory.Bimod.restrictLeft (RAlgIso(A)).hom (Mon.trivial _)

/-- Lower shriek of right DG modules induced by a monoidal adjunction satisfying the projection
formula.  Its carrier is the ambient left-adjoint image of the original module complex. -/
@[stacks 0FRW "lower shriek of right differential graded modules"]
noncomputable def functor (A : DGA(OD)) :
    Mod(RAlg(A), d) ⥤ Mod(A, d) :=
  normalize (R := R) A ⋙ adj.rightModuleLowerShriek A.toMon ⋙ ofBimodFunctor A

/-- The underlying complex of DG lower shriek is the ambient lower shriek of the underlying
complex; coefficient normalization does not replace the carrier. -/
@[simp]
theorem functor_obj_toComplex (A : DGA(OD))
    (M : Mod(RAlg(A), d)) :
    ((functor adj A).obj M).toComplex = L.obj M.toComplex := sorry

/-- Restriction of DG modules applies the ambient monoidal right adjoint to the underlying
complex. -/
@[simp]
theorem restriction_obj_toComplex (A : DGA(OD)) (N : Mod(A, d)) :
    ((restriction (R := R) A).obj N).toComplex = R.obj N.toComplex := sorry

/-- Restriction of a left DG module applies the ambient monoidal right adjoint to its carrier. -/
@[simp]
theorem restrictionLeft_obj_X (A : DGA(OD))
    (N : DifferentialGradedAlgebra.LeftModule (J := JD) (𝒪 := OD) A) :
    ((restrictionLeft (R := R) A).obj N).X = R.obj N.X := sorry

/-- The lifted adjunction between lower shriek and restriction of right DG modules. -/
@[stacks 0FRW "lower shriek-restriction adjunction for DG modules"]
noncomputable def adjunction (A : DGA(OD)) :
    functor adj A ⊣ restriction (R := R) A :=
  (((toBimodEquivalence (RAlg(A))).toAdjunction.comp
      (CategoryTheory.Bimod.restrictRightEquivalence
        (RAlgIso(A))).toAdjunction).comp
    (adj.rightModuleAdjunction A.toMon)).comp
      (toBimodEquivalence A).symm.toAdjunction

/-- The reusable Hom equivalence for lower shriek and restriction of right DG modules. -/
@[stacks 0FRW "lower shriek-restriction Hom equivalence for DG modules"]
noncomputable def homEquiv (A : DGA(OD))
    (M : Mod(RAlg(A), d)) (N : Mod(A, d)) :
    ((functor adj A).obj M ⟶ N) ≃
      (M ⟶ (restriction (R := R) A).obj N) :=
  (adjunction adj A).homEquiv M N

end SheafOfModules.RingedSite.DifferentialGradedModule.LowerShriek

end
