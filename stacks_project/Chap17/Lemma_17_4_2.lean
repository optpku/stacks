/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.GeneratingSections.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open SheafOfModules.GeneratingSections

noncomputable section

universe u

variable {X : RingedSpace.{u}} {ℱ : X.Modules} {I : Type u}
variable (s : I → ℱ.sections)

/- Lemma 17.4.2: a family of global sections generates a module sheaf exactly when its germs
span the stalk at every point. -/
@[stacks 01AN]
#check (CommRing.epi_iff_stalkSpan_eq_top s :
  Epi (ℱ.freeHomEquiv.symm s) ↔ ∀ x : X, CommRing.stalkSpan s x = ⊤)

/- A chosen generating family therefore spans every stalk. -/
#check @CommRing.stalkSpan_eq_top
