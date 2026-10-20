/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import ReasLib.Algebra.Homology.CochainComplex.Bimod.Flat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Forget
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.GradedModule.Bimod
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Bimod
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative flatness for differential graded modules

The two local tensor conditions used in the definition of a good DG module are kept atomic:
flatness after forgetting the differential but retaining the graded algebra action, and
K-flatness for the actual relative DG tensor product.  Universal base-change stability belongs in
a separate layer because it changes the ambient ringed topos and algebra.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule
open scoped SheafOfModules.RingedSite.LeftDifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable {𝒪 : Sheaf J CommRingCat.{w}} {A : DGA(𝒪)}

/-- A right DG `A`-module is graded-flat when forgetting its differential gives a flat graded
right module over the underlying graded algebra of `A`. -/
@[stacks 0FSA "graded relative flatness"]
def IsGradedFlat (M : Mod(A, d)) : Prop :=
  CategoryTheory.Bimod.IsGradedFlat
    (C := DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := 𝒪))
    (A := A.toMon) (toBimod M)

/-- Graded-flat right DG `A`-modules as an object property. -/
abbrev gradedFlatObjects (A : DGA(𝒪)) : ObjectProperty Mod(A, d) :=
  fun M ↦ IsGradedFlat M

/-- A right DG `A`-module is relatively K-flat when tensoring it with every acyclic left DG
`A`-module gives an acyclic cochain complex. -/
@[stacks 0FSA "relative K-flatness"]
def IsKFlat (M : Mod(A, d)) : Prop :=
  CategoryTheory.Bimod.IsKFlat
    (C := DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := 𝒪))
    (A := A.toMon) (toBimod M)

/-- Relatively K-flat right DG `A`-modules as an object property. -/
abbrev kFlatObjects (A : DGA(𝒪)) : ObjectProperty Mod(A, d) :=
  fun M ↦ IsKFlat M

/-- The two relative tensor conditions for goodness at the current base ringed site and algebra. -/
@[stacks 0FSA "goodness conditions at a fixed base"]
def IsGoodAtBase (M : Mod(A, d)) : Prop :=
  CategoryTheory.Bimod.IsGoodAtBase
    (C := DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := 𝒪))
    (A := A.toMon) (toBimod M)

/-- DG modules satisfying both local tensor conditions as an object property. -/
abbrev goodAtBaseObjects (A : DGA(𝒪)) : ObjectProperty Mod(A, d) :=
  fun M ↦ IsGoodAtBase M

/-- Graded flatness is exactness of the true relative graded tensor functor after forgetting the
differential. -/
theorem isGradedFlat_iff (M : Mod(A, d)) :
    IsGradedFlat M ↔
      DifferentialGradedAlgebra.GradedModule.IsFlat ((forgetToGraded A).obj M) := sorry

/-- Relative K-flatness is preservation of acyclicity by the true relative DG tensor functor. -/
theorem isKFlat_iff (M : Mod(A, d)) :
    IsKFlat M ↔
      ∀ N : LMod(A, d), HomologicalComplex.Acyclic N.X →
        HomologicalComplex.Acyclic (tensor M N) := sorry

/-- The local goodness predicate is exactly graded relative flatness together with relative
K-flatness. -/
theorem isGoodAtBase_iff (M : Mod(A, d)) :
    IsGoodAtBase M ↔ IsGradedFlat M ∧ IsKFlat M := sorry

end

end SheafOfModules.RingedSite.DifferentialGradedModule

end
