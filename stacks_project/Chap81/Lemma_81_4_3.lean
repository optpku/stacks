module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap81.Lemma_81_4_2_Pseudofunctor

/-!
# Lemma 81.4.3

A representable morphism of algebraic spaces that is surjective integral,
surjective proper, or surjective flat and locally of finite presentation
satisfies descent for Type-valued sheaves on the small étale site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleSheaf

/-- Lemma 81.4.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. If `f` is representable by schemes and is either surjective and
integral, surjective and proper, or surjective and flat and locally of finite
presentation, then the functor from Type-valued sheaves on the small étale site
of `Y` to singleton descent data along `{f}` is an equivalence of categories. -/
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
  sorry

/-- If `f` is representable by schemes and surjective proper, then
`pseudofunctor.toDescentData` of the singleton family `{f}` is an equivalence. -/
theorem descentIsEquivalenceOfRepresentableProper
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) [Surjective f] [Proper f] :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  sorry

/-- If `f` is representable by schemes, surjective, flat, and locally of finite
presentation, then `pseudofunctor.toDescentData` of the singleton family `{f}`
is an equivalence. -/
theorem descentIsEquivalenceOfRepresentableFlat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) [Surjective f] [Flat f]
    [LocallyOfFinitePresentation f] :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleSheaf
