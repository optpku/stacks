module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay.Locus

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.22.7 (1): for a flat, locally finitely presented morphism, the
Cohen--Macaulay-at-point locus is the locus where the local ring of the fibre is
Cohen--Macaulay. -/
@[stacks 045U]
#check (AlgebraicGeometry.Scheme.Hom.cohenMacaulayLocus_eq_fiberStalk :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f],
    {x : X | f.CohenMacaulayAt x} =
      {x : X | CohenMacaulayRing (fiberStalkAt f x)})

/- Lemma 37.22.7 (2): the Cohen--Macaulay-at-point locus of a flat, locally
finitely presented morphism is open. -/
@[stacks 045U]
#check (AlgebraicGeometry.Scheme.Hom.isOpen_cohenMacaulayLocus :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f],
    IsOpen {x : X | f.CohenMacaulayAt x})

/- Lemma 37.22.7 (3): the Cohen--Macaulay-at-point locus of a flat, locally
finitely presented morphism is dense in every scheme-theoretic fibre. -/
@[stacks 045U]
#check (AlgebraicGeometry.Scheme.Hom.dense_cohenMacaulayLocus_fiber :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (s : S),
    Dense ((f.fiberι s) ⁻¹' {x : X | f.CohenMacaulayAt x}))

/- Lemma 37.22.7 (4): the Cohen--Macaulay-at-point locus of a flat, locally
finitely presented morphism commutes with arbitrary base change. -/
@[stacks 045U]
#check (AlgebraicGeometry.Scheme.Hom.cohenMacaulayLocus_eq_preimage_of_isPullback :
  ∀ {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (hcart : IsPullback g' f' f g)
    [Flat f] [LocallyOfFinitePresentation f],
    {x' : X' | f'.CohenMacaulayAt x'} =
      g' ⁻¹' {x : X | f.CohenMacaulayAt x})

end AlgebraicGeometry.Scheme.Hom
