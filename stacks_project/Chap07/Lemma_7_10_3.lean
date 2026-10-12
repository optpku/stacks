/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef

public import Mathlib.CategoryTheory.Sites.Plus

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (P : Cᵒᵖ ⥤ Type (max u v))

/- Domain-style sampling for Lemma 7.10.3:
- primary domain: the plus construction for set-valued presheaves on a Grothendieck site;
- sampled owner API:
  `CategoryTheory.GrothendieckTopology.plusObj`,
  `CategoryTheory.GrothendieckTopology.toPlus`,
  `CategoryTheory.GrothendieckTopology.toPlusNatTrans`,
  `CategoryTheory.Presheaf.isLocallySurjective_toPlus`;
- source-facing layer: the source introduces the plus construction `P ↦ P⁺` and its canonical map;
- core/canonical owner: `J.plusObj P` and `J.toPlus P`;
- bridge/view: the functorial packaging `J.plusFunctor` and `J.toPlusNatTrans`.

Primitive data are only the topology `J` and the presheaf `P`. The map `J.toPlus P` is derived
from the owner construction, so this file should remain a direct recall of the canonical API
rather than introduce a local wrapper.
-/
/-
Lemma 7.10.3: the plus construction on a set-valued presheaf `P` canonically gives the presheaf
`P⁺`.
-/
@[stacks 00W4] #check J.plusObj P

/- Companion recall: the plus construction comes with the canonical map of presheaves
`J.toPlus P : P ⟶ P⁺`. -/
@[stacks 00W4 "canonical map to the plus construction"]
#check J.toPlus P
