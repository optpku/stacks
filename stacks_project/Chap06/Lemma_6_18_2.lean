/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Sheafification.AddCommGrp
public import ReasLib.Topology.Sheaves.Abelian
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat
open scoped TopCat

noncomputable section

universe u

variable {X : TopCat.{u}}

local notation "J" => Opens.grothendieckTopology X

variable (ℱ : PAb(X)) (𝒢 : Ab(X))

/- Lemma 6.18.2 (1): the set-valued sheafification of an abelian presheaf has a unique
compatible abelian-group structure for which the sheafification map is a morphism of abelian
presheaves, and the resulting abelian presheaf is a sheaf. -/
@[stacks 0085 "unique abelian sheaf structure on the fixed set-valued sheafification"]
#check CategoryTheory.GrothendieckTopology.existsUniqueCompatibleAddCommGroupStructure_sheafify J ℱ

/- Lemma 6.18.2 (2): sheafification of abelian presheaves is left adjoint to the inclusion of
abelian sheaves into abelian presheaves. -/
@[stacks 0085 "adjunction between abelian presheaf sheafification and inclusion"]
#check (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv ℱ 𝒢).symm :
  (ℱ ⟶ 𝒢.obj) ≃ ((presheafToSheaf J AddCommGrpCat.{u}).obj ℱ ⟶ 𝒢))
