module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.OpenImmersion

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineSpace

/-- For a field of positive characteristic, every finite étale morphism to a closed subscheme of
affine space is an open and closed subscheme of the pullback of a finite étale morphism over the
ambient affine space. -/
theorem existsFiniteEtaleClopenExtension
    {k : Type u} [Field k] (p n : ℕ) [CharP k p] (h_positiveChar : 0 < p)
    {Z Y : Scheme.{u}} (i : Z ⟶ 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of.{u} k)))
    [IsClosedImmersion i] (g : Y ⟶ Z) [IsFinite g] [Etale g] :
    ∃ (U : Scheme.{u})
      (f : U ⟶ 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of.{u} k))),
      (IsFinite f ∧ Etale f) ∧
        ∃ (j : Y ⟶ pullback f i),
          IsOpenImmersion j ∧ IsClosedImmersion j ∧ j ≫ pullback.snd f i = g := sorry

end AlgebraicGeometry.AffineSpace
