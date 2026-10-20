module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback

/-!
# Relations on an algebraic space over a base

This module records pre-relations and relations in the slice category of algebraic spaces over a
base algebraic space.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]

#check (PreRelation : ∀ {B : AlgebraicSpace S}, Over B → Type (u + 1))

end AlgebraicGeometry.AlgebraicSpace
