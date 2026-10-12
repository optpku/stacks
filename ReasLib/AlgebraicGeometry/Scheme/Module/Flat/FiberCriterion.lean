/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.Noetherian

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For a coherent quasi-coherent module with nonzero stalk on locally Noetherian schemes,
flatness over the base together with flatness on the fibre is equivalent to flatness of the
intermediate scheme over the base together with relative flatness over the intermediate scheme. -/
theorem flatOverAt_and_fiber_iff {S X Y : Scheme.{u}}
    [IsLocallyNoetherian S] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (g : Y ⟶ S) (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsCoherent] (x : X)
    (h_stalk : ¬ IsZero (RingedSpace.stalkModuleCat ℱ x)) :
    (flatOverAt ℱ (f ≫ g) x ∧
      flatOverAt ((pullback ((f ≫ g).fiberι (g (f x)))).obj ℱ)
        (Scheme.Hom.compFiberToBaseFiber f g (g (f x))) ((f ≫ g).asFiber x)) ↔
      (Scheme.Hom.flatAt g (f x) ∧ flatOverAt ℱ f x) := sorry

end AlgebraicGeometry.Scheme.Modules
