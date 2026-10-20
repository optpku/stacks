module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pushforward.Fiber
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback

/-!
# Eventual cohomology vanishing from ampleness on a fibre

For proper morphisms to Noetherian schemes, ampleness of an invertible module
on one fibre yields a common eventual twist bound for higher-direct-image
stalk vanishing and surjectivity of restriction to fibre sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An invertible module ample on a fibre of a proper morphism to a Noetherian
scheme gives a common eventual twist bound for vanishing of all positive
higher-direct-image stalks and surjectivity of canonical restriction from the
ordinary pushforward stalk to global sections on that fibre. -/
theorem exists_twist_bound_of_isAmple_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian Y] [IsProper f]
    (L : X.Modules) [L.Invertible] (F : X.Modules) [F.IsCoherent] (y : Y)
    [Scheme.Modules.IsAmple ((Scheme.Modules.pullback (f.fiberι y)).obj L)] :
    ∃ d0 : ℕ, ∀ d : ℕ, d0 ≤ d →
      (∀ p : ℕ, 0 < p →
        IsZero (RingedSpace.stalkModuleCat
          (RingedSpace.Hom.higherDirectImageModule f.toShHom (F ⊗ L ^⊗ (d : ℤ)) p) y)) ∧
      Function.Surjective (stalkToFiberSections f (F ⊗ L ^⊗ (d : ℤ)) y).hom := sorry

end AlgebraicGeometry.Scheme.Hom
