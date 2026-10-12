/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.RingTheory.RingHom.Quotient
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change for ideal-power torsion modules

This is the degree-zero formal-gluing interface. It owns the restriction of
extension of scalars to ideal-power torsion modules, its equivalence criterion,
and the induced comparison on morphisms.

@stack 05E7
@stack 05E9
@stack 05EC
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace ModuleCat.IdealPower.BaseChange

section Restricted

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Extension of scalars sends ideal-power torsion modules to modules supported
on powers of the extended ideal. -/
theorem extendScalars_isIdealPowerTorsion (f : R →+* S) (I : Ideal R)
    (M : ModuleCat R) (hM : Module.IsIdealPowerTorsion I M) :
    Module.IsIdealPowerTorsion (I.map f) ((ModuleCat.extendScalars f).obj M) := sorry

/-- Extension of scalars restricted to the full subcategories of ideal-power
torsion modules. -/
@[stacks 05E7 "ideal-power torsion base-change functor",
  stacks 05E9 "ideal-power torsion base-change functor",
  stacks 05EC "ideal-power torsion base-change functor"]
noncomputable def restricted (f : R →+* S) (I : Ideal R) :
    CategoryTheory.ObjectProperty.FullSubcategory
        (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) ⥤
      CategoryTheory.ObjectProperty.FullSubcategory
        (fun M : ModuleCat S ↦ Module.IsIdealPowerTorsion (I.map f) M) :=
  CategoryTheory.ObjectProperty.lift
    (fun M : ModuleCat S ↦ Module.IsIdealPowerTorsion (I.map f) M)
    (CategoryTheory.ObjectProperty.ι
        (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) ⋙
      ModuleCat.extendScalars f)
    (fun M ↦ extendScalars_isIdealPowerTorsion f I M.obj M.property)

/-- Lemma 15.90.3 (3) (05EC): flat base change inducing an
isomorphism modulo `I` is an equivalence on ideal-power torsion modules. -/
@[stacks 05EC "equivalence of ideal-power torsion modules"]
theorem restricted_isEquivalence (f : R →+* S) (I : Ideal R)
    (hI : I.FG) (hflat : f.Flat)
    (hquot : Function.Bijective (f.quotientByIdeal I)) :
    Functor.IsEquivalence (restricted f I) := sorry

end Restricted

section Hom

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Lemma 15.90.3 (Tag 05EC): extension of scalars is fully faithful on a Hom pair when either
module is ideal-power torsion. -/
@[stacks 05EC]
theorem homMap_bijective (f : R →+* S) (I : Ideal R) (hI : I.FG) (hf : f.Flat)
    {M N : ModuleCat.{u} R}
    (hMN : Module.IsIdealPowerTorsion I M ∨ Module.IsIdealPowerTorsion I N)
    (hquot : Function.Bijective (f.quotientByIdeal I)) :
    Function.Bijective
      (fun g : M ⟶ N ↦ (ModuleCat.extendScalars f).map g) := sorry

end Hom

end ModuleCat.IdealPower.BaseChange
