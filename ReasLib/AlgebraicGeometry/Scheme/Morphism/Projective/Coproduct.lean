module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Coproduct
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.Coproduct

/-!
# Projective morphisms from finite coproducts

This file records projectivity of the morphism induced from a finite family of projective
morphisms over a base admitting an ample invertible module.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- The morphism from a finite coproduct induced by projective morphisms is projective when the
base admits an ample invertible module. -/
theorem Projective.sigmaDesc_of_hasAmpleInvertibleModule
    {ι : Type u} [Finite ι] {S : Scheme.{u}}
    (hS : Scheme.Modules.HasAmpleInvertibleModule S)
    (X : ι → Scheme.{u}) (f : ∀ i, X i ⟶ S) (hf : ∀ i, Projective (f i)) :
    Projective (Sigma.desc f) := sorry

end AlgebraicGeometry
