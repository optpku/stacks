module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Syntomic
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_36_4_Syntomic

/-!
# Syntomic covering families of algebraic spaces

A syntomic covering of an algebraic space is an indexed family of syntomic
morphisms that is jointly surjective on points.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.SyntomicCovering :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    {ι : Type v}, (ι → CategoryTheory.Over X) → Prop)

end AlgebraicGeometry.AlgebraicSpace
