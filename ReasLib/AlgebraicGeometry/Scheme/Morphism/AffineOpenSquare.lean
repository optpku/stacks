/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A flat scheme morphism induces a flat algebra map on the affine sources of a
commutative square whose horizontal maps are open immersions. -/
theorem flatOfOpenSquare
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]
    (i : Spec (CommRingCat.of R) ⟶ S) [IsOpenImmersion i]
    (hcomm : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ i) :
    Module.Flat R A := sorry

/-- A locally finitely presented scheme morphism induces a finitely presented
algebra map on the affine sources of a commutative square whose horizontal maps
are open immersions. -/
theorem finitePresentationOfOpenSquare
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]
    (i : Spec (CommRingCat.of R) ⟶ S) [IsOpenImmersion i]
    (hcomm : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ i) :
    Algebra.FinitePresentation R A := sorry

end AlgebraicGeometry.Scheme.Hom
