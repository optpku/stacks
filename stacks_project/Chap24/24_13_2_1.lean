/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Forget.Exact
import StacksCheckRecall

@[expose] public section
open CategoryTheory CategoryTheory.Limits SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}} (A : DGA(O))
variable (S : ShortComplex Mod(A, d)) (hS : S.ShortExact) (n : ℤ)

/- 24.13.2.1: the actual short exact sequence of DG-module sheaves yields the long cohomology
sequence of its underlying cochain complexes. Its first maps are induced by S.f and S.g;
the third is the canonical connecting morphism. There is no extra underlying-exactness premise. -/
@[stacks 0FRK "long exact cohomology sequence of DG-module sheaves"] #check
  (SheafOfModules.RingedSite.DifferentialGradedModule.homologySequence_exact A S hS n :
    (HomologicalComplex.HomologySequence.composableArrows₅
      (SheafOfModules.RingedSite.DifferentialGradedModule.shortExact_forgetToComplex A S hS)
      n (n+1) (ComplexShape.up_mk n (n+1) rfl)).Exact)
