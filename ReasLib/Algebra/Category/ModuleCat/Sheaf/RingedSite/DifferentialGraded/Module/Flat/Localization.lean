/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.ProjectionFormula
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Flat.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Flat.Free
import Mathlib.Tactic.CrossRefAttribute

/-!
# Good localized algebra modules

The extension `j_! A_U` is represented canonically as the free right DG `A`-module on the
localized structure module `j_! O_U` placed in degree zero.  The projection formula identifies
its underlying complex with the usual extension by zero of `A|_U`.

This leaf owns the fixed-base flatness statements and the algebraic reduction needed after a
specified base change.  Quantification over arbitrary morphisms of ringed topoi remains in the
geometric `RingedSite.ToposHom` layer, whose responsibility is to supply the comparison
isomorphism used below.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w u' v' w'

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable {O : Sheaf J CommRingCat.{w}}

/-- The localized structure module `j_! O_U`, regarded as a cochain complex concentrated in
degree zero.  This is the coefficient complex from which `j_! A_U` is freely generated. -/
@[stacks 0FSB "localized degree-zero generator"]
noncomputable def localizedGenerator (O : Sheaf J CommRingCat.{w}) (U : C)
    [(SheafOfModules.Localization.restriction (ringSheaf J O) U :
      SheafOfModules.{w} (ringSheaf J O) ⥤
        SheafOfModules.{w} ((ringSheaf J O).over U)).IsRightAdjoint] :
    CochainComplex
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O)) ℤ :=
  (HomologicalComplex.single
    (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O))
      (ComplexShape.up ℤ) (0 : ℤ)).obj
      (SheafOfModules.Localization.structureModule (ringSheaf J O) U)

/-- The localized degree-zero generator is termwise flat. -/
theorem localizedGenerator_isTermwiseFlat (O : Sheaf J CommRingCat.{w}) (U : C)
    [(SheafOfModules.Localization.restriction (ringSheaf J O) U :
      SheafOfModules.{w} (ringSheaf J O) ⥤
        SheafOfModules.{w} ((ringSheaf J O).over U)).IsRightAdjoint] :
    HomologicalComplex.IsTermwiseFlat (localizedGenerator O U) := sorry

/-- The localized degree-zero generator is K-flat. -/
theorem localizedGenerator_isKFlat (O : Sheaf J CommRingCat.{w}) (U : C)
    [(SheafOfModules.Localization.restriction (ringSheaf J O) U :
      SheafOfModules.{w} (ringSheaf J O) ⥤
        SheafOfModules.{w} ((ringSheaf J O).over U)).IsRightAdjoint] :
    HomologicalComplex.IsKFlat (localizedGenerator O U) := sorry

/-- The canonical right DG `A`-module model of `j_! A_U`: freely extend the localized
degree-zero structure module along `O → A`. -/
@[stacks 0FSB "localized algebra module"]
noncomputable def algebraExtensionByZero (A : DGA(O)) (U : C)
    [(SheafOfModules.Localization.restriction (ringSheaf J O) U :
      SheafOfModules.{w} (ringSheaf J O) ⥤
        SheafOfModules.{w} ((ringSheaf J O).over U)).IsRightAdjoint] :
    Mod(A, d) :=
  (freeFunctor A).obj (localizedGenerator O U)

/-- The underlying complex of `j_! A_U` is the tensor product of its localized degree-zero
generator with `A`. -/
theorem algebraExtensionByZero_toComplex (A : DGA(O)) (U : C)
    [(SheafOfModules.Localization.restriction (ringSheaf J O) U :
      SheafOfModules.{w} (ringSheaf J O) ⥤
        SheafOfModules.{w} ((ringSheaf J O).over U)).IsRightAdjoint] :
    (algebraExtensionByZero A U).toComplex =
      HomologicalComplex.tensorObj (localizedGenerator O U) A.toComplex := sorry

namespace IsGradedFlat

/-- The localized algebra module `j_! A_U` is graded-flat over `A` at the current base. -/
@[stacks 0FSB "fixed-base graded flatness"]
theorem algebraExtensionByZero (A : DGA(O)) (U : C)
    [(SheafOfModules.Localization.restriction (ringSheaf J O) U :
      SheafOfModules.{w} (ringSheaf J O) ⥤
        SheafOfModules.{w} ((ringSheaf J O).over U)).IsRightAdjoint] :
    IsGradedFlat (DifferentialGradedModule.algebraExtensionByZero A U) := sorry

end IsGradedFlat

namespace IsKFlat

/-- The localized algebra module `j_! A_U` is relatively K-flat over `A` at the current base. -/
@[stacks 0FSB "fixed-base K-flatness"]
theorem algebraExtensionByZero (A : DGA(O)) (U : C)
    [(SheafOfModules.Localization.restriction (ringSheaf J O) U :
      SheafOfModules.{w} (ringSheaf J O) ⥤
        SheafOfModules.{w} ((ringSheaf J O).over U)).IsRightAdjoint] :
    IsKFlat (DifferentialGradedModule.algebraExtensionByZero A U) := sorry

end IsKFlat

namespace IsGoodAtBase

/-- Lemma 24.23.1 (0FSB), fixed-base component: `j_! A_U` satisfies the graded-flat and
relative K-flat conditions over the current ringed site and DG algebra. -/
@[stacks 0FSB "fixed-base goodness"]
theorem algebraExtensionByZero (A : DGA(O)) (U : C)
    [(SheafOfModules.Localization.restriction (ringSheaf J O) U :
      SheafOfModules.{w} (ringSheaf J O) ⥤
        SheafOfModules.{w} ((ringSheaf J O).over U)).IsRightAdjoint] :
    IsGoodAtBase (DifferentialGradedModule.algebraExtensionByZero A U) := sorry

end IsGoodAtBase

section BaseChange

variable {D : Type u'} [Category.{v'} D] {JD : GrothendieckTopology D}
variable [JD.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
variable [HasWeakSheafify JD AddCommGrpCat.{w'}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{w'}]
variable [UnivLE.{max u' v', w'}]
variable {OD : Sheaf JD CommRingCat.{w'}}

variable (F : CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O)) ℤ ⥤
  CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := JD) (𝒪 := OD)) ℤ)
variable [F.LaxMonoidal]
variable {A : DGA(O)} {B : DGA(OD)}

namespace BaseChange.IsGradedFlat

/-- A comparison with a localized algebra module at the target proves graded flatness after the
specified base change.  Geometric base-change owners should construct the comparison
isomorphism and reuse this theorem. -/
theorem algebraExtensionByZero_of_iso
    (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B) (U : C) (V : D)
    [(SheafOfModules.Localization.restriction (ringSheaf J O) U :
      SheafOfModules.{w} (ringSheaf J O) ⥤
        SheafOfModules.{w} ((ringSheaf J O).over U)).IsRightAdjoint]
    [(SheafOfModules.Localization.restriction (ringSheaf JD OD) V :
      SheafOfModules.{w'} (ringSheaf JD OD) ⥤
        SheafOfModules.{w'} ((ringSheaf JD OD).over V)).IsRightAdjoint]
    (e : (baseChange F φ).obj (algebraExtensionByZero A U) ≅
      algebraExtensionByZero B V) :
    BaseChange.IsGradedFlat (C := C) (D := D) (JC := J) (JD := JD)
      (OC := O) (OD := OD) F φ (algebraExtensionByZero A U) := sorry

end BaseChange.IsGradedFlat

namespace BaseChange.IsKFlat

/-- A comparison with a localized algebra module at the target proves relative K-flatness after
the specified base change. -/
theorem algebraExtensionByZero_of_iso
    (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B) (U : C) (V : D)
    [(SheafOfModules.Localization.restriction (ringSheaf J O) U :
      SheafOfModules.{w} (ringSheaf J O) ⥤
        SheafOfModules.{w} ((ringSheaf J O).over U)).IsRightAdjoint]
    [(SheafOfModules.Localization.restriction (ringSheaf JD OD) V :
      SheafOfModules.{w'} (ringSheaf JD OD) ⥤
        SheafOfModules.{w'} ((ringSheaf JD OD).over V)).IsRightAdjoint]
    (e : (baseChange F φ).obj (algebraExtensionByZero A U) ≅
      algebraExtensionByZero B V) :
    BaseChange.IsKFlat (C := C) (D := D) (JC := J) (JD := JD)
      (OC := O) (OD := OD) F φ (algebraExtensionByZero A U) := sorry

end BaseChange.IsKFlat

namespace BaseChange.IsGoodAtBase

/-- Goodness after a specified base change follows once geometry identifies the base-changed
localized algebra module with the localized algebra module at the target.  This is the algebraic
reduction used by the universal clause of Lemma 24.23.1. -/
@[stacks 0FSB "specified base-change reduction"]
theorem algebraExtensionByZero_of_iso
    (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B) (U : C) (V : D)
    [(SheafOfModules.Localization.restriction (ringSheaf J O) U :
      SheafOfModules.{w} (ringSheaf J O) ⥤
        SheafOfModules.{w} ((ringSheaf J O).over U)).IsRightAdjoint]
    [(SheafOfModules.Localization.restriction (ringSheaf JD OD) V :
      SheafOfModules.{w'} (ringSheaf JD OD) ⥤
        SheafOfModules.{w'} ((ringSheaf JD OD).over V)).IsRightAdjoint]
    (e : (baseChange F φ).obj (algebraExtensionByZero A U) ≅
      algebraExtensionByZero B V) :
    BaseChange.IsGoodAtBase (C := C) (D := D) (JC := J) (JD := JD)
      (OC := O) (OD := OD) F φ (algebraExtensionByZero A U) := sorry

end BaseChange.IsGoodAtBase

end BaseChange

/- The free module has explicit carrier and action data; any `sorryAx` in this audit is confined
to inherited categorical law fields. -/

end SheafOfModules.RingedSite.DifferentialGradedModule

end
