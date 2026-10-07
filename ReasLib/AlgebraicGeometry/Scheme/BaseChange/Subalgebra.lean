module

public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Affine

/-!
# Affine base change along a subalgebra

This leaf records the canonical map from base change along `A → B` to base
change along a subalgebra `A' ⊆ B`.  The construction is independent of any
finite-generation or descent theorem.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme.AffineBaseChange.Subalgebra

/-- The canonical morphism from the affine base change along `A → B` to the one along
the subalgebra `A' ⊆ B`. -/
noncomputable abbrev map
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (A' : Subalgebra A B) :
    Scheme.AffineBaseChange.baseChange A B f ⟶ Scheme.AffineBaseChange.baseChange A A' f :=
  Scheme.AffineBaseChange.mapAlg f A'.val

/-- The subalgebra base-change map commutes with projection to the source scheme. -/
theorem map_toSource
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (A' : Subalgebra A B) :
    map f A' ≫ Scheme.AffineBaseChange.toSource A A' f =
      Scheme.AffineBaseChange.toSource A B f := sorry

/-- The subalgebra base-change map commutes with projection to the subalgebra spectrum. -/
theorem map_toBase
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (A' : Subalgebra A B) :
    map f A' ≫ Scheme.AffineBaseChange.toBase A A' f =
      Scheme.AffineBaseChange.toBase A B f ≫ Spec.map (CommRingCat.ofHom (A'.val : A' →+* B)) := sorry

end Scheme.AffineBaseChange.Subalgebra

end AlgebraicGeometry
