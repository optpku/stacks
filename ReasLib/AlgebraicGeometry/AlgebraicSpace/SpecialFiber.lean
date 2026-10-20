module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Special fibres of algebraic spaces

The quotient map of a ring determines a morphism of algebraic spaces over its
spectrum. Pulling back along this morphism gives the special fibre over an ideal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {A : Type u} [CommRing A]

/-- The morphism `Spec(A ⧸ I) ⟶ Spec A` induced by the quotient map, viewed as a
morphism of algebraic spaces over `Spec A`. -/
abbrev specQuotientι (I : Ideal A) :
    ofOver (Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ⟶
      ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))) :=
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  SchemeRealization.ofOverMap (Over.homMk q (Category.comp_id q))

/-- The special fibre `X ×_{Spec A} Spec(A ⧸ I)`, viewed as an algebraic space
over `Spec A`. -/
abbrev fiberOverQuotient (I : Ideal A) (X : AlgebraicSpace (Spec (CommRingCat.of A))) :
    AlgebraicSpace (Spec (CommRingCat.of A)) :=
  pullback (SchemeRealization.toBase X) (specQuotientι I)

end AlgebraicGeometry.AlgebraicSpace
