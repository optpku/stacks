/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafPseudofunctor

/-!
# Representable descent for small étale sheaves

Surjective representable morphisms that are integral, proper, or flat and locally
of finite presentation satisfy descent for Type-valued small étale sheaves.
The same holds for a morphism admitting a composite with these properties.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleSheaf

/-- For a morphism of algebraic spaces over a scheme that is representable by
schemes and is either surjective integral, surjective proper, or surjective flat
and locally of finite presentation, the canonical functor from Type-valued small
étale sheaves on the target to singleton descent data is an equivalence. -/
@[stacks 0GFU]
theorem descentIsEquivalenceOfRepresentable
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) [Surjective f]
    (h : IsIntegralHom f ∨ Proper f ∨ (Flat f ∧ LocallyOfFinitePresentation f)) :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  sorry

/-- If `f` is representable by schemes and surjective integral, then
`pseudofunctor.toDescentData` of the singleton family `{f}` is an equivalence. -/
theorem descentIsEquivalenceOfRepresentableIntegral
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) [Surjective f] [IsIntegralHom f] :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  descentIsEquivalenceOfRepresentable f hf (Or.inl inferInstance)

/-- If `f` is representable by schemes and surjective proper, then
`pseudofunctor.toDescentData` of the singleton family `{f}` is an equivalence. -/
theorem descentIsEquivalenceOfRepresentableProper
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) [Surjective f] [Proper f] :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  descentIsEquivalenceOfRepresentable f hf (Or.inr (Or.inl inferInstance))

/-- If `f` is representable by schemes, surjective, flat, and locally of finite
presentation, then `pseudofunctor.toDescentData` of the singleton family `{f}`
is an equivalence. -/
theorem descentIsEquivalenceOfRepresentableFlat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) [Surjective f] [Flat f]
    [LocallyOfFinitePresentation f] :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  descentIsEquivalenceOfRepresentable f hf
    (Or.inr (Or.inr ⟨inferInstance, inferInstance⟩))

/-- Canonical singleton descent for a surjective integral morphism representable
by schemes is an equivalence of categories of Type-valued small étale sheaves. -/
instance singletonDescent_isEquivalence_of_representableIntegral
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Fact (yoneda.relativelyRepresentable f)] [Surjective f] [IsIntegralHom f] :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  descentIsEquivalenceOfRepresentableIntegral f Fact.out

/-- Canonical singleton descent for a surjective proper morphism representable
by schemes is an equivalence of categories of Type-valued small étale sheaves. -/
instance singletonDescent_isEquivalence_of_representableProper
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Fact (yoneda.relativelyRepresentable f)] [Surjective f] [Proper f] :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  descentIsEquivalenceOfRepresentableProper f Fact.out

/-- Canonical singleton descent for a surjective, flat, locally finitely presented
morphism representable by schemes is an equivalence of categories of Type-valued
small étale sheaves. -/
instance singletonDescent_isEquivalence_of_representableFlat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Fact (yoneda.relativelyRepresentable f)] [Surjective f] [Flat f]
    [LocallyOfFinitePresentation f] :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  descentIsEquivalenceOfRepresentableFlat f Fact.out

/-- If a composite `π ≫ f` of morphisms of algebraic spaces over a scheme is
representable by schemes and is either surjective integral, surjective proper,
or surjective flat and locally of finite presentation, then the canonical
functor from Type-valued small étale sheaves on the target of `f` to singleton
descent data along `f` is an equivalence. -/
@[stacks 0GFV]
theorem descentIsEquivalenceOfRepresentableComposite
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {X' : AlgebraicSpace S} (π : X' ⟶ X)
    (hπf : yoneda.relativelyRepresentable (π ≫ f)) [Surjective (π ≫ f)]
    (h : IsIntegralHom (π ≫ f) ∨ Proper (π ≫ f) ∨
      (Flat (π ≫ f) ∧ LocallyOfFinitePresentation (π ≫ f))) :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  sorry

/-- If `π ≫ f` is representable by schemes and surjective integral, then
`pseudofunctor.toDescentData` of the singleton family `{f}` is an equivalence. -/
theorem descentIsEquivalenceOfRepresentableCompositeIntegral
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {X' : AlgebraicSpace S} (π : X' ⟶ X)
    (hπf : yoneda.relativelyRepresentable (π ≫ f)) [Surjective (π ≫ f)]
    [IsIntegralHom (π ≫ f)] :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  descentIsEquivalenceOfRepresentableComposite f π hπf (Or.inl inferInstance)

/-- If `π ≫ f` is representable by schemes and surjective proper, then
`pseudofunctor.toDescentData` of the singleton family `{f}` is an equivalence. -/
theorem descentIsEquivalenceOfRepresentableCompositeProper
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {X' : AlgebraicSpace S} (π : X' ⟶ X)
    (hπf : yoneda.relativelyRepresentable (π ≫ f)) [Surjective (π ≫ f)]
    [Proper (π ≫ f)] :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  descentIsEquivalenceOfRepresentableComposite f π hπf (Or.inr (Or.inl inferInstance))

/-- If `π ≫ f` is representable by schemes, surjective, flat, and locally of
finite presentation, then `pseudofunctor.toDescentData` of the singleton
family `{f}` is an equivalence. -/
theorem descentIsEquivalenceOfRepresentableCompositeFlat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {X' : AlgebraicSpace S} (π : X' ⟶ X)
    (hπf : yoneda.relativelyRepresentable (π ≫ f)) [Surjective (π ≫ f)]
    [Flat (π ≫ f)] [LocallyOfFinitePresentation (π ≫ f)] :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  descentIsEquivalenceOfRepresentableComposite f π hπf
    (Or.inr (Or.inr ⟨inferInstance, inferInstance⟩))

end AlgebraicGeometry.AlgebraicSpace.EtaleSheaf
