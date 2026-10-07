module

public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.ShortExact

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Module.Determinant TensorProduct

universe u v

#check (@CategoryTheory.ShortComplex.ShortExact.exteriorComparison :
  ∀ {R : Type u} [CommRing R] {S : ShortComplex (ModuleCat.{v} R)}
    {N : ModuleCat.{v} R} (_ : S.ShortExact) (dL : N ⟶ S.X₂) (dM : N ⟶ S.X₃)
    (_ : dL ≫ S.g = dM) [Module.Free R N] [Module.Finite R N]
    [Module.Free R S.X₃] [Module.Finite R S.X₃]
    (_ : Module.finrank R N = Module.finrank R S.X₃) (p : ℕ),
    (cokernel dL).exteriorPower p →ₗ[R]
      S.X₁.exteriorPower p ⊗[R] (det[R](N) →ₗ[R] det[R](S.X₃)))
