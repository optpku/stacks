/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Retract.FiniteCoproduct
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.StrictlyPerfect
public import ReasLib.Algebra.Homology.CochainComplex.MappingCone.BoundedTermsIn

/-!
# Mapping cones of strictly perfect complexes

Strict perfectness is stable under mapping cones because boundedness is stable under mapping
cones and finite-free retracts are stable under binary coproducts.  The theorem is valid over an
arbitrary sheaf of rings on an arbitrary site.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules
namespace CochainComplex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable {R : Sheaf J RingCat.{w}}

/-- Mapping cones preserve termwise finite-free retractness. -/
theorem IsTermwiseFiniteFreeRetract.mappingCone
    {K L : _root_.CochainComplex (SheafOfModules R) ℤ} (f : K ⟶ L)
    [HomologicalComplex.HasHomotopyCofiber f]
    (hK : IsTermwiseFiniteFreeRetract K) (hL : IsTermwiseFiniteFreeRetract L) :
    IsTermwiseFiniteFreeRetract (_root_.CochainComplex.mappingCone f) := sorry

/-- Lemma 20.46.2 (08C5) and Lemma 21.44.2 (08FM): the mapping cone of a morphism between
strictly perfect complexes is strictly perfect. -/
@[stacks 08C5, stacks 08FM]
theorem IsStrictlyPerfect.mappingCone
    {K L : _root_.CochainComplex (SheafOfModules R) ℤ} (f : K ⟶ L)
    [HomologicalComplex.HasHomotopyCofiber f]
    (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L) :
    IsStrictlyPerfect (_root_.CochainComplex.mappingCone f) := sorry

end CochainComplex
end SheafOfModules
