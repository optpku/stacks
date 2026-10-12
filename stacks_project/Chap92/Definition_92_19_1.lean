/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.«92_19_0_2_Triangle»
import StacksCheckRecall

open SheafOfModules.RingedSite.CotangentComplex
open scoped SheafOfModules.RingedSite.CotangentComplex

/- Definition 92.19.1: Let C be a site. Let A ⟶ B be a homomorphism of sheaves
of rings. Let F be a sheaf of B-modules. The map F ⟶ (L_{B/A} ⊗^L_B F)⟦1⟧
in 92.19.0.2 is called the Atiyah class of F. This is connectingMap,
equivalently the third arrow of atiyahTriangle. -/
@[stacks 09DI]
#check connectingMap

#check atiyahTriangle_mor₃
#check tensorModule
