/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra
import StacksCheckRecall

@[expose] public section

/- Definition 24.12.1 (1): a sheaf of differential graded 𝒪-algebras on a ringed site
(C, 𝒪) is a cochain complex of 𝒪-modules with associative unital 𝒪-bilinear
multiplication maps A n × A m ⟶ A (n + m) satisfying the graded Leibniz rule. -/
@[stacks 0FRF] #check SheafOfModules.RingedSite.DifferentialGradedAlgebra

/- Definition 24.12.1 (2): a homomorphism of differential graded 𝒪-algebras is a
map of complexes of 𝒪-modules compatible with the multiplication maps. -/
@[stacks 0FRF] #check SheafOfModules.RingedSite.DifferentialGradedAlgebra.Hom
