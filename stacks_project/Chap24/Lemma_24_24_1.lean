/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.GradedHull
import StacksCheckRecall

/-!
# Lemma 24.24.1

The reusable owner is the differential graded hull adjunction in ReasLib.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}}
variable (A : DGA(O))

/- Lemma 24.24.1 (0FSK): the forgetful functor from differential graded modules to graded
modules admits a specified differential graded hull as a left adjoint. -/
@[stacks 0FSK]
#check @GradedHull.nonempty

/- The standard Mathlib right-adjoint interface is available without selecting public data. -/
#check (forgetToGraded_isRightAdjoint A : (forgetToGraded A).IsRightAdjoint)

/- A caller-supplied hull exposes its functor and adjunction directly. -/
variable (G H : GradedHull A)

#check (G.toFunctor : A.GradedModule ⥤ Mod(A, d))
#check (G.adjunction : G.toFunctor ⊣ forgetToGraded A)

/- The public data are independent of the specified hull up to the unique adjoint isomorphism. -/
#check (G.iso H : G.toFunctor ≅ H.toFunctor)

end SheafOfModules.RingedSite.DifferentialGradedModule

end
