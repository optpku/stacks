/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Flat.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 24.23.1

The canonical model of `j_! A_U` is a genuine right DG `A`-module: the free module on the
localized structure module `j_! O_U` in degree zero.  Its two fixed-base goodness conditions are
owned separately by the reusable flatness API.

The source also requires the same conditions after every morphism of ringed topoi and every
extension of the pulled-back DG algebra.  That universal clause is not replaced here by the
strictly weaker pullback along a chosen continuous functor of sites.  Its remaining owner is the
still-missing geometric `RingedSite.ToposHom` specialization of DG-module base change.
-/

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w uD vD wD

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable {O : Sheaf J CommRingCat.{w}}
variable (A : DGA(O)) (U : C)
variable [(SheafOfModules.Localization.restriction (ringSheaf J O) U :
  SheafOfModules.{w} (ringSheaf J O) ⥤
    SheafOfModules.{w} ((ringSheaf J O).over U)).IsRightAdjoint]

/- Lemma 24.23.1 (0FSB), canonical object: the reusable DG-module model of `j_! A_U`. -/
@[stacks 0FSB "canonical localized algebra module"]
#check (algebraExtensionByZero A U : Mod(A, d))

/- Lemma 24.23.1 (0FSB), fixed-base condition (1): `j_! A_U` is graded-flat over `A`. -/
@[stacks 0FSB "fixed-base graded flatness"]
#check
  (IsGradedFlat.algebraExtensionByZero A U :
    IsGradedFlat (algebraExtensionByZero A U))

/- Lemma 24.23.1 (0FSB), fixed-base condition (2): `j_! A_U` is relatively K-flat over `A`. -/
@[stacks 0FSB "fixed-base K-flatness"]
#check
  (IsKFlat.algebraExtensionByZero A U :
    IsKFlat (algebraExtensionByZero A U))

/- Lemma 24.23.1 (0FSB), conjunction of the two fixed-base goodness conditions. -/
@[stacks 0FSB "fixed-base goodness"]
#check
  (IsGoodAtBase.algebraExtensionByZero A U :
    IsGoodAtBase (algebraExtensionByZero A U))

/- Lemma 24.23.1 (0FSB), universal-clause reduction: after a specified algebraic base change,
it suffices for the geometric layer to identify the result with a localized algebra module at
the target. -/
section BaseChangeReduction

variable {D : Type uD} [Category.{vD} D] {JD : GrothendieckTopology D}
variable [JD.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
variable [HasWeakSheafify JD AddCommGrpCat.{wD}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{wD}]
variable [UnivLE.{max uD vD, wD}]
variable {OD : Sheaf JD CommRingCat.{wD}}
variable (F : CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O)) ℤ ⥤
  CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := JD) (𝒪 := OD)) ℤ)
variable [F.LaxMonoidal] (B : DGA(OD))
variable (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B) (V : D)
variable [(SheafOfModules.Localization.restriction (ringSheaf JD OD) V :
  SheafOfModules.{wD} (ringSheaf JD OD) ⥤
    SheafOfModules.{wD} ((ringSheaf JD OD).over V)).IsRightAdjoint]
variable (e : (baseChange F φ).obj (algebraExtensionByZero A U) ≅
  algebraExtensionByZero B V)

@[stacks 0FSB "specified base-change reduction"]
#check
  (BaseChange.IsGoodAtBase.algebraExtensionByZero_of_iso F φ U V e :
    BaseChange.IsGoodAtBase
      (C := C) (D := D) (JC := J) (JD := JD) (OC := O) (OD := OD)
      (A := A) (B := B) F φ (algebraExtensionByZero A U))

end BaseChangeReduction

/- The projection-formula model exposes the underlying complex as `j_! O_U[0] ⊗ A`. -/
#check
  (algebraExtensionByZero_toComplex A U :
    (algebraExtensionByZero A U).toComplex =
      HomologicalComplex.tensorObj (localizedGenerator O U) A.toComplex)

end SheafOfModules.RingedSite.DifferentialGradedModule

end
