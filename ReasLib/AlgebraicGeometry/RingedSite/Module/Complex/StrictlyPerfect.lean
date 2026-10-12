/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Retract
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.StrictlyPerfect
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic

@[expose] public section

/-!
# Strictly perfect complexes on ringed sites

This module specializes the general strictly-perfect complex API for module sheaves to bundled
ringed sites, and provides the corresponding site-presented bridge for a commutative ring sheaf.
-/

open CategoryTheory

noncomputable section

universe u v w

namespace RingedSite
namespace CochainComplex

section

variable {X : RingedSite.{u, v, w}}
variable [UnivLE.{max u v, w}]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{w}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Strictly perfect complexes on a bundled ringed site, as an object property. -/
@[stacks 08FL]
abbrev strictlyPerfect :
    ObjectProperty (CochainComplex (ModuleCat.{w} X) ℤ) :=
  _root_.SheafOfModules.CochainComplex.strictlyPerfect
    (R := X.structureSheaf)

/-- A complex of modules on a bundled ringed site is strictly perfect when it belongs to
`strictlyPerfect`. -/
abbrev IsStrictlyPerfect
    (E : CochainComplex (ModuleCat.{w} X) ℤ) : Prop :=
  strictlyPerfect E

/-- Strictly perfect complexes on a bundled ringed site, as a full subcategory. -/
abbrev StrictlyPerfect :=
  (strictlyPerfect (X := X)).FullSubcategory

namespace StrictlyPerfect

/-- The canonical inclusion of strictly perfect complexes on a ringed site. -/
abbrev ι : StrictlyPerfect (X := X) ⥤ CochainComplex (ModuleCat.{w} X) ℤ :=
  ObjectProperty.ι _

end StrictlyPerfect

/-- A strictly perfect complex on a ringed site has explicit lower and upper bounds. -/
theorem IsStrictlyPerfect.bounded
    {E : CochainComplex (ModuleCat.{w} X) ℤ} (hE : IsStrictlyPerfect E) :
    ∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b := sorry

/-- Every term of a strictly perfect complex on a ringed site lies in the finite-free retract
closure. -/
theorem IsStrictlyPerfect.term_retractClosure
    {E : CochainComplex (ModuleCat.{w} X) ℤ} (hE : IsStrictlyPerfect E)
    (i : ℤ) :
    SheafOfModules.finiteFreeRetractModuleProperty X.structureSheaf (E.X i) := sorry

/-- Strict perfectness on a bundled ringed site unfolds to explicit strict bounds and termwise
finite-free retract closure. -/
@[stacks 08FL "explicit characterization"]
theorem isStrictlyPerfect_iff
    (E : CochainComplex (ModuleCat.{w} X) ℤ) :
    IsStrictlyPerfect E ↔
      (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
        ∀ i : ℤ, SheafOfModules.finiteFreeRetractModuleProperty X.structureSheaf (E.X i) := sorry

end

section

variable {X : RingedSite.{u, v, w}}
variable [UnivLE.{max u v, w}]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{w}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [X.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

/-- Each term of a strictly perfect complex on a ringed site is a retract of a finite free module
sheaf. -/
theorem IsStrictlyPerfect.term_retract_free
    {E : CochainComplex (ModuleCat.{w} X) ℤ} (hE : IsStrictlyPerfect E)
    (i : ℤ) :
    ∃ I : Type w, Finite I ∧
      Nonempty (Retract (E.X i)
        (_root_.SheafOfModules.free I : ModuleCat.{w} X)) := sorry

end

end CochainComplex
end RingedSite
