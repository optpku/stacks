module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap68.Definition_68_3_1_FiberDegree
public import stacks_project.Chap68.Lemma_68_12_8_Decent

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions

/-!
# Relative property (β), decent, and reasonable morphisms

The space-level and relative conditions are defined in their mathematical owners.
The typed checks and public imports retain the chapter's existing interface.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.HasPropertyBeta :
  ∀ {S : Scheme.{u}}, AlgebraicSpace S → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.IsReasonable :
  ∀ {S : Scheme.{u}}, AlgebraicSpace S → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.PropertyBeta :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Decent :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Reasonable :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)
