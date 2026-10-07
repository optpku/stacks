module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Coproduct
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Ample

/-!
# Quasi-projective morphisms from finite coproducts

This file records quasi-projectivity of the morphism induced from a finite family of
quasi-projective morphisms over a base admitting an ample invertible module.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- The morphism from a finite coproduct induced by quasi-projective morphisms is
quasi-projective when the base admits an ample invertible module. -/
theorem QuasiProjective.sigmaDesc_of_hasAmpleInvertibleModule
    {ι : Type u} [Finite ι] {S : Scheme.{u}}
    (hS : Scheme.Modules.HasAmpleInvertibleModule S)
    (X : ι → Scheme.{u}) (f : ∀ i, X i ⟶ S) (hf : ∀ i, QuasiProjective (f i)) :
    QuasiProjective (Sigma.desc f) := sorry

end AlgebraicGeometry
