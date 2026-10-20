module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.NegativeCohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.RegularSection

/-!
# Connectedness of zero schemes of ample sections

This file records a connectedness criterion for the zero scheme of a regular section of an ample
invertible module on a proper scheme over a field.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsAmple

/-- The zero scheme of a regular global section of an ample invertible module on a connected
scheme proper over a field is connected when all closed-point local rings have depth at least
two. -/
theorem connectedSpace_zeroScheme
    {k : Type u} [Field k] {X : Scheme.{u}} [ConnectedSpace X]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (L : X.Modules) [L.Invertible] [IsAmple L]
    (s : L.sections)
    (hs : RingedSpace.IsRegularSection L s)
    (hdepth : ∀ x : X, x ∈ closedPoints X →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x)) :
    ConnectedSpace (Scheme.zeroScheme L s) := sorry

end AlgebraicGeometry.Scheme.Modules.IsAmple
