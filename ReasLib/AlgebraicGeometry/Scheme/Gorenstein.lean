module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.RingTheory.Gorenstein.Local

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme is Gorenstein if it is locally Noetherian and all of its local rings are
Gorenstein. -/
class Gorenstein (X : Scheme.{u}) : Prop where
  /-- A Gorenstein scheme is locally Noetherian. -/
  isLocallyNoetherian : IsLocallyNoetherian X
  /-- Every local ring of a Gorenstein scheme is Gorenstein. -/
  stalkIsGorenstein (x : X) : IsGorensteinLocalRing (X.presheaf.stalk x)

namespace Gorenstein

/-- A Gorenstein scheme carries its canonical locally Noetherian instance. -/
instance instIsLocallyNoetherian (X : Scheme.{u}) [h : Gorenstein X] :
    IsLocallyNoetherian X := h.isLocallyNoetherian

end Gorenstein

/-- Gorenstein schemes are exactly the locally Noetherian schemes whose local rings are
Gorenstein. -/
theorem gorenstein_iff (X : Scheme.{u}) :
    Gorenstein X ↔
      IsLocallyNoetherian X ∧
        ∀ x : X, IsGorensteinLocalRing (X.presheaf.stalk x) := sorry

end AlgebraicGeometry.Scheme
