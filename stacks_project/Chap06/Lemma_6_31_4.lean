/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.ExtensionByInitial
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat TopologicalSpace

noncomputable section

universe u

/-
The source states the set-valued case, but every clause depends only on an initial object and the
standard exactness hypotheses needed for sheafification and stalks. Lemma 6.31.7 is therefore the
canonical owner: specializing its coefficient category to `Type u` recovers extension by the empty
set, while its atomic inside/outside stalk statements avoid a noncanonical by-cases wrapper.
-/

section

variable {X : TopCat.{u}}
variable (U : Opens X)
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]

/- Lemma 6.31.4 (1): on presheaves of sets over an open subset `U ⊆ X`, extension by the empty set
is left adjoint to restriction to `U`. -/
@[stacks 00A3 "presheaf extension by the empty set is left adjoint to restriction"]
#check
  (TopCat.Presheaf.ExtensionByInitial.Properties.adjunction
    (C := Type u) U)

/- Lemma 6.31.4 (2): on sheaves of sets over an open subset `U ⊆ X`, extension by the empty set
is left adjoint to restriction to `U`. -/
@[stacks 00A3 "sheaf extension by the empty set is left adjoint to restriction"]
#check
  (TopCat.Sheaf.ExtensionByInitial.Properties.adjunction
    (C := Type u) U)

variable (ℱ : (TopCat.Opens.Subspace.space U).Sheaf (Type u))

/- Lemma 6.31.4 (3), inside `U`: the stalk of the extension-by-empty sheaf `j_! ℱ` is canonically
isomorphic to the stalk of `ℱ`. -/
@[stacks 00A3 "stalk of extension by the empty set inside the open subset"]
#check fun (x : TopCat.Opens.Subspace.space U) ↦
  TopCat.Sheaf.ExtensionByInitial.Properties.stalkIso_of_mem
    (C := Type u) U ℱ x

/- Lemma 6.31.4 (3), outside `U`: the stalk of the extension-by-empty sheaf `j_! ℱ` is canonically
isomorphic to the empty set. -/
@[stacks 00A3 "stalk of extension by the empty set outside the open subset"]
#check fun (x : X) (hx : x ∉ (U : Set X)) ↦
  TopCat.Sheaf.ExtensionByInitial.Properties.stalk_isInitial_of_not_mem
    (C := Type u) U ℱ x hx

/- Lemma 6.31.4 (4): on presheaves over `U`, the unit `𝟭 ⟶ j_p j_{p!}` is a natural
isomorphism. -/
@[stacks 00A3 "presheaf restriction after extension by the empty set"]
#check
  (TopCat.Presheaf.ExtensionByInitial.Properties.unit_isIso
    (C := Type u) U)

/- Lemma 6.31.4 (5): on sheaves over `U`, the unit `𝟭 ⟶ j⁻¹ j_!` is a natural isomorphism. -/
@[stacks 00A3 "sheaf restriction after extension by the empty set"]
#check
  (TopCat.Sheaf.ExtensionByInitial.Properties.unit_isIso
    (C := Type u) U)

end
