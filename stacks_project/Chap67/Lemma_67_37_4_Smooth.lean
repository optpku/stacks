module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap65.Definition_65_12_5_ZariskiCover
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_5_2_Surjective

/-!
# Smooth morphisms of algebraic spaces

A morphism of algebraic spaces is smooth when every étale scheme square over it
has smooth top arrow, in the sense of Stacks Definition 67.37.1 (1).
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.SmoothAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.smoothAt_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X),
    SmoothAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Smooth (i ≫ f))

#check (AlgebraicGeometry.AlgebraicSpace.pullbackAlongSchemeFunctorOfPoints :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {V : Over S} (b : ofOver V ⟶ Y),
    (Over S)ᵒᵖ ⥤ Type u)

#check (AlgebraicGeometry.AlgebraicSpace.pullbackAlongSchemeFstNat :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {V : Over S} (b : ofOver V ⟶ Y),
    pullbackAlongSchemeFunctorOfPoints f b ⟶ X.functorOfPoints)

#check (AlgebraicGeometry.AlgebraicSpace.pullbackAlongSchemeSndNat :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {V : Over S} (b : ofOver V ⟶ Y),
    pullbackAlongSchemeFunctorOfPoints f b ⟶ (ofOver V).functorOfPoints)

#check (AlgebraicGeometry.AlgebraicSpace.pullbackAlongScheme :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : ofOver V ⟶ Y),
    AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.pullbackAlongScheme.fst :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) {V : Over S}
    (b : ofOver V ⟶ Y),
    pullbackAlongScheme f b ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.pullbackAlongScheme.snd :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) {V : Over S}
    (b : ofOver V ⟶ Y),
    pullbackAlongScheme f b ⟶ ofOver V)

#check (AlgebraicGeometry.AlgebraicSpace.pullbackAlongScheme.functorOfPoints_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : ofOver V ⟶ Y),
    (pullbackAlongScheme f b).functorOfPoints =
      pullbackAlongSchemeFunctorOfPoints f b)

#check (AlgebraicGeometry.AlgebraicSpace.pullbackAlongScheme.fst_comp :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : ofOver V ⟶ Y),
    pullbackAlongScheme.fst f b ≫ f = pullbackAlongScheme.snd f b ≫ b)

#check (AlgebraicGeometry.AlgebraicSpace.pullbackAlongScheme.isPullback :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : ofOver V ⟶ Y),
    IsPullback (pullbackAlongScheme.fst f b) (pullbackAlongScheme.snd f b) f b)

#check (AlgebraicGeometry.AlgebraicSpace.Smooth.baseChangeOnSchemes :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Smooth.baseChangeOnAffineSchemes :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Smooth.existsSurjectiveEtaleTarget :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Smooth.existsSurjectiveEtaleSource :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Smooth.forallEtaleSquare :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Smooth.existsEtaleSquare :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Smooth.existsZariskiCover.{u, v} :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Prop)

end AlgebraicGeometry.AlgebraicSpace
