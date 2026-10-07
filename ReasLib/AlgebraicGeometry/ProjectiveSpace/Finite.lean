module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.FiniteType
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace ProjectiveSpace

/-- A finite type algebra over a Noetherian ring whose spectrum is a closed
immersion into projective space is finite as a module over the base ring. -/
@[stacks 0EG6]
theorem moduleFinite_of_closedImmersion
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B] {n : ℕ}
    (i : Spec (.of B) ⟶ scheme A n) [IsClosedImmersion i]
    (hfactor : i ≫ toSpec A n = Spec.map (CommRingCat.ofHom (algebraMap A B))) :
    Module.Finite A B := sorry

/-- A finite morphism of commutative rings gives a closed immersion of its spectrum into
some standard projective space over the spectrum of the source ring. -/
theorem exists_closedImmersion_of_finite {R S : CommRingCat.{u}} {f : R ⟶ S}
    (hf : f.hom.Finite) :
    ∃ (n : ℕ) (i : Spec S ⟶ ProjectiveSpace.scheme R n),
      IsClosedImmersion i ∧ i ≫ ProjectiveSpace.toSpec R n = Spec.map f := sorry

end ProjectiveSpace
end AlgebraicGeometry
