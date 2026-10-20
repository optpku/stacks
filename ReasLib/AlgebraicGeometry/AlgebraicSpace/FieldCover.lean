module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Field-spectrum morphisms into an algebraic space with a flat surjective field cover

If an algebraic space admits a surjective flat morphism from the spectrum of a
field, every morphism from the spectrum of a field is surjective and flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If an algebraic space over a scheme admits a surjective flat morphism from
the spectrum of a field, then every morphism from the spectrum of a field into
that algebraic space is surjective and flat. -/
theorem surjective_and_flat_of_specField_cover {S : Scheme.{u}} {Z : AlgebraicSpace S}
    {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (cover : ofOver (Over.mk σ) ⟶ Z) [Surjective cover] [Flat cover]
    {k' : Type u} [Field k'] {σ' : Spec (.of k') ⟶ S}
    (f : ofOver (Over.mk σ') ⟶ Z) : Surjective f ∧ Flat f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
