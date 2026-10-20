/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.GradedHull
import StacksCheckRecall

/-!
# Lemma 24.24.2

The three properties of the differential graded hull are exposed as atomic ReasLib statements.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule
open scoped DifferentialGradedAlgebra.GradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}}
variable (A : DGA(O)) (G : GradedHull A) (N : A.GradedModule)

/- Lemma 24.24.2 (0FSL) (1): the hull unit is monic. -/
@[stacks 0FSL "(1)"]
#check (GradedHull.unit_mono G N : Mono ((G.unit).app N))

/- Lemma 24.24.2 (0FSL) (2): the canonical bar differential is an isomorphism of graded
modules, not merely degreewise. -/
@[stacks 0FSL "(2)"]
#check (GradedHull.barD_isIso G N : IsIso (G.barD N))

/- Lemma 24.24.2 (0FSL) (3): the differential graded hull is acyclic. -/
@[stacks 0FSL "(3)"]
#check
  (G.acyclic N : HomologicalComplex.Acyclic (G.toFunctor.obj N).toComplex)

/- The bar differential is reusable as a single graded-module morphism. -/
#check (G.barD N : N ⟶ (G.cokernel N)[1])
#check (G.barD_hom N)

end SheafOfModules.RingedSite.DifferentialGradedModule

end
