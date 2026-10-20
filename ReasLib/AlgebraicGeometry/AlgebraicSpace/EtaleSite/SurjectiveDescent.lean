module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafPseudofunctor

/-!
# Surjective descent for small étale sheaves

Surjective morphisms of algebraic spaces that are integral, proper, or flat and
locally of finite presentation satisfy descent for Type-valued small étale sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleSheaf

/-- For a morphism of algebraic spaces over a scheme that is either surjective
and integral, surjective and proper, or surjective and flat and locally of finite
presentation, the canonical functor from Type-valued small étale sheaves on the
target to singleton descent data is an equivalence of categories. -/
@[stacks 0GFW]
theorem descentIsEquivalenceOfSurjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Surjective f]
    (h : IsIntegralHom f ∨ Proper f ∨ (Flat f ∧ LocallyOfFinitePresentation f)) :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  sorry

/-- If `f` is surjective integral, then `pseudofunctor.toDescentData` of the
singleton family `{f}` is an equivalence. -/
@[instance]
theorem descentIsEquivalenceOfSurjectiveIntegral
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Surjective f] [IsIntegralHom f] :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  descentIsEquivalenceOfSurjective f (Or.inl inferInstance)

/-- If `f` is surjective proper, then `pseudofunctor.toDescentData` of the
singleton family `{f}` is an equivalence. -/
@[instance]
theorem descentIsEquivalenceOfSurjectiveProper
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Surjective f] [Proper f] :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  descentIsEquivalenceOfSurjective f (Or.inr (Or.inl inferInstance))

/-- If `f` is surjective, flat, and locally of finite presentation, then
`pseudofunctor.toDescentData` of the singleton family `{f}` is an equivalence. -/
@[instance]
theorem descentIsEquivalenceOfSurjectiveFlat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f] :
    (pseudofunctor.toDescentData (fun _ : PUnit ↦ f)).IsEquivalence :=
  descentIsEquivalenceOfSurjective f (Or.inr (Or.inr ⟨inferInstance, inferInstance⟩))

end AlgebraicGeometry.AlgebraicSpace.EtaleSheaf
