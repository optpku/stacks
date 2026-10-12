/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products of fixed-base good acyclic DG modules

For differential graded module sheaves on a ringed site, the two fixed-base goodness conditions
imply that an acyclic right module remains acyclic after tensoring with an arbitrary left module.
The proof uses a good left resolution; universal stability under morphisms of ringed topoi belongs
to the separate geometric base-change layer.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule
open scoped SheafOfModules.RingedSite.LeftDifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule.IsGoodAtBase

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}} {A : DGA(O)}

/-- Lemma 24.23.8 (0FSI), fixed-base tensor clause: a fixed-base good acyclic right DG module
has acyclic tensor product with every left DG module. -/
@[stacks 0FSI "(1), fixed-base tensor clause"]
theorem tensor_acyclic {P : Mod(A, d)} (hP : IsGoodAtBase P)
    (hPacyclic : HomologicalComplex.Acyclic P.toComplex) (N : LMod(A, d)) :
    HomologicalComplex.Acyclic (tensor P N) := sorry

end SheafOfModules.RingedSite.DifferentialGradedModule.IsGoodAtBase

end
