module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.AlgebraicSpace
public import stacks_project.Chap65.Lemma_65_16_4_IsAlgebraicSpace
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap79.«79_12_0_2»
public import stacks_project.Chap79.Lemma_79_12_1_Hom

/-!
# The finite part of a separated locally finite-type morphism

If `f : X ⟶ Y` is separated and locally of finite type, then the finite-part
functor `(X/Y)_fin` is an algebraic space and the structure morphism
`(X/Y)_fin ⟶ Y` is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Proposition 79.12.11 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism
of algebraic spaces over `S` which is separated and locally of finite type.
Then `(X/Y)_fin` is an algebraic space. -/
@[stacks 04QH] #check (AlgebraicGeometry.AlgebraicSpace.FinitePart.instIsAlgebraicSpace :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] [LocallyOfFiniteType f], IsAlgebraicSpace (finitePart f))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.space :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] [LocallyOfFiniteType f], AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.space_functorOfPoints :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] [LocallyOfFiniteType f],
    (AlgebraicGeometry.AlgebraicSpace.FinitePart.space f).functorOfPoints = finitePart f)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.spaceHom :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] [LocallyOfFiniteType f],
    AlgebraicGeometry.AlgebraicSpace.FinitePart.space f ⟶ Y)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.spaceHom_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] [LocallyOfFiniteType f],
    AlgebraicGeometry.AlgebraicSpace.FinitePart.spaceHom f =
      AlgebraicGeometry.AlgebraicSpace.FinitePart.toY f)

/- Proposition 79.12.11 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism
of algebraic spaces over `S` which is separated and locally of finite type.
Then the morphism `(X/Y)_fin ⟶ Y` is étale. -/
@[stacks 04QH] #check (AlgebraicGeometry.AlgebraicSpace.FinitePart.instEtale_spaceHom :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] [LocallyOfFiniteType f],
    Etale (AlgebraicGeometry.AlgebraicSpace.FinitePart.spaceHom f))
