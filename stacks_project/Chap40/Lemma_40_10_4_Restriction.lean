/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap39.Lemma_39_18_1_Restriction
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Field

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)
variable {k k' : Type u} [Field k] [Field k']
variable (eU : Spec (CommRingCat.of k) ≅ G.U.left) (ι : k →+* k')

/- The field-spectrum morphism used by the compatibility import is provided by the shared
restriction API. -/
#check (fieldRestrictionMap G eU ι : Spec (CommRingCat.of k') ⟶ G.U.left)

/- The field-extension object over the base scheme is provided by the shared restriction API. -/
#check (fieldRestrictionOver G eU ι : Over S)

/- The canonical morphism from the field-extension object is provided by the shared restriction
API. -/
#check (fieldRestriction G eU ι : fieldRestrictionOver G eU ι ⟶ G.U)

end AlgebraicGeometry.GroupoidScheme
