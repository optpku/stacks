module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A proper clopen open subscheme of the special fibre of a separated finite-type scheme over
a henselian pair lifts to a proper clopen open subscheme of the original scheme. -/
theorem exists_clopen_proper_lift
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f] [FiniteType f]
    (I : Ideal A) [HenselianRing A I]
    (Y : (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).Opens)
    (hY : IsClopen
      (Y : Set (CategoryTheory.Limits.pullback f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme)))
    [IsProper
      (Y.ι ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))] :
    ∃ W : X.Opens,
      IsClopen (W : Set X) ∧ IsProper (W.ι ≫ f) ∧
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
          pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⟶ X) ⁻¹ᵁ W = Y := sorry

end AlgebraicGeometry.Scheme.Hom
