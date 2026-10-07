module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints
import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.Fiber

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For a finite-type quasicoherent module flat over the base at a point, weak association
to its tensor product with a pulled-back quasicoherent module is equivalent to weak association
on the base together with association on the corresponding fiber. -/
@[stacks 05IH]
theorem mem_weakAss_tensor_pullback_iff_of_flatOverAt
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (𝒢 : S.Modules) [𝒢.IsQuasicoherent] (x : X)
    (h_flat : flatOverAt ℱ f x) :
    x ∈ (ℱ ⊗ (Scheme.Modules.pullback f).obj 𝒢).weakAss ↔
      f x ∈ 𝒢.weakAss ∧
        f.asFiber x ∈
          ((Scheme.Modules.pullback (f.fiberι (f x))).obj ℱ).associatedPoints := sorry

/-- The weakly associated points of the tensor product of a finite-type quasicoherent module
flat over the base with a pulled-back quasicoherent module are the images of the associated
points of its fibers over the weakly associated points on the base. -/
@[stacks 05IJ]
theorem weakAss_tensor_pullback_eq_iUnion_fiber_associatedPoints
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (𝒢 : S.Modules) [𝒢.IsQuasicoherent] (h_flat : flatOver ℱ f) :
    (ℱ ⊗ (Scheme.Modules.pullback f).obj 𝒢).weakAss =
      ⋃ s ∈ 𝒢.weakAss,
        f.fiberι s '' ((Scheme.Modules.pullback (f.fiberι s)).obj ℱ).associatedPoints := sorry

end AlgebraicGeometry.Scheme.Modules
