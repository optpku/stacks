/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex
import StacksCheckRecall

@[expose] public section

open CategoryTheory SheafOfModules.RingedSite.CotangentComplex

universe u

/- Definition 92.18.1: Let C be a site. Let A ⟶ B be a homomorphism of sheaves of
rings on C. The standard resolution of B over A is the augmentation ε : P_• ⟶ B
with terms P_0 = A[B], P_1 = A[A[B]], … and maps as constructed above. -/
@[stacks 08SR]
#check (SheafOfModules.RingedSite.CotangentComplex.standardResolution :
  ∀ {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget CommRingCat.{u})] [HasWeakSheafify J CommRingCat.{u}]
    (A : Sheaf J CommRingCat.{u}) (B : Under A), SimplicialObject.Augmented (Under A))

#check @standardResolution_obj_zero
#check @standardTerm
#check @standardAugmentation
#check @standardMap
#check @freeForgetAdjunction
#check @standardResolution_right
