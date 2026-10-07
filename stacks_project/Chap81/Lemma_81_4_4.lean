module

public import stacks_project.Chap81.Lemma_81_4_3

/-!
# Lemma 81.4.4

If a composite morphism of algebraic spaces is representable by schemes and
is surjective integral, surjective proper, or surjective flat and locally of
finite presentation, then Type-valued sheaves on the small étale site of the
target are equivalent to singleton descent data along the coarser morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleSheaf

/-- Lemma 81.4.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `π : X' ⟶ X` be a morphism of algebraic spaces. If
`π ≫ f` is representable by schemes and is either surjective and integral,
surjective and proper, or surjective and flat and locally of finite
presentation, then the functor from Type-valued sheaves on the small étale site
of `Y` to singleton descent data along `{f}` is an equivalence of categories. -/
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
  sorry

/-- If `π ≫ f` is representable by schemes and surjective proper, then
`pseudofunctor.toDescentData` of the singleton family `{f}` is an equivalence. -/
theorem descentIsEquivalenceOfRepresentableCompositeProper
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {X' : AlgebraicSpace S} (π : X' ⟶ X)
    (hπf : yoneda.relativelyRepresentable (π ≫ f)) [Surjective (π ≫ f)]
    [Proper (π ≫ f)] :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  sorry

/-- If `π ≫ f` is representable by schemes, surjective, flat, and locally of
finite presentation, then `pseudofunctor.toDescentData` of the singleton
family `{f}` is an equivalence. -/
theorem descentIsEquivalenceOfRepresentableCompositeFlat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {X' : AlgebraicSpace S} (π : X' ⟶ X)
    (hπf : yoneda.relativelyRepresentable (π ≫ f)) [Surjective (π ≫ f)]
    [Flat (π ≫ f)] [LocallyOfFinitePresentation (π ≫ f)] :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleSheaf
