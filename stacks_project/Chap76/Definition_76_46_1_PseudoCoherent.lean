module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Remark_67_22_3_EtaleLocal
public import stacks_project.Chap67.Remark_67_22_8_OpenAt

/-!
# Pseudo-coherent morphisms of algebraic spaces

A morphism of algebraic spaces is pseudo-coherent when every étale scheme square
over it has pseudo-coherent top arrow, in the sense of Stacks Definition 76.46.1
(1). Pointwise pseudo-coherence is pseudo-coherence after restriction to an
open subspace neighbourhood.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

#check (AlgebraicGeometry.AlgebraicSpace.PseudoCoherent :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.PseudoCoherentAt :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y), AlgebraicGeometry.AlgebraicSpace.Points X → Prop)
