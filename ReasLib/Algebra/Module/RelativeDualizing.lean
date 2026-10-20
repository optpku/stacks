module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.OpenImmersion.BasicOpen
public import ReasLib.LinearAlgebra.TensorProduct.RightModule
public import ReasLib.RingTheory.QuasiFinite.FiniteType

@[expose] public section

open AlgebraicGeometry
open scoped TensorProduct TensorProduct.Right

universe u v w

namespace Algebra

namespace DualModule

/-- The `B`-module structure on the `A`-linear dual of an `A`-algebra `B`, given by
precomposition with multiplication in `B`. -/
abbrev module (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] :
    Module B (Module.Dual A B) :=
  { smul := fun b f ↦ Module.Dual.transpose (LinearMap.mulLeft A b) f
    one_smul := sorry
    mul_smul := sorry
    smul_zero := sorry
    smul_add := sorry
    add_smul := sorry
    zero_smul := sorry }

end DualModule

-- The scoped registration is opt-in because this dual action competes with other module descriptions.
scoped[Algebra.DualModule] attribute [instance 100] Algebra.DualModule.module
open scoped Algebra.DualModule

namespace DualModule

/-- The `A`-linear dual of an `A`-algebra `B`, bundled with its `B`-module structure. -/
abbrev of (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] :
    ModuleCat B :=
  @ModuleCat.of B _ (Module.Dual A B) _ (module A B)

/-- The action in `Algebra.DualModule.of A B` satisfies `(b • f) x = f (b * x)`. -/
theorem smul_apply
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (b x : B) (f : of A B) :
    (b • f : Module.Dual A B) x = (f : Module.Dual A B) (b * x) := sorry

end DualModule

namespace RelativeDualizingModule

/-- The relative dualizing `B`-module associated to a chosen finite factorization
`A → B' → B` whose induced map `Spec B → Spec B'` is an open immersion. -/
def of
    (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    (_h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (_h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))) :
    ModuleCat B :=
  @ModuleCat.of B _ (DualModule.of A B' ⊗[B'] B) _ TensorProduct.Right.module

/-- The chosen-factorization relative dualizing module is the scalar extension of
`Algebra.DualModule.of A B'` from `B'` to `B`. -/
theorem of_eq
    (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))) :
    RelativeDualizingModule.of A B' B h_quasiFinite h_open =
      @ModuleCat.of B _ (DualModule.of A B' ⊗[B'] B) _ TensorProduct.Right.module := sorry

end RelativeDualizingModule

end Algebra
