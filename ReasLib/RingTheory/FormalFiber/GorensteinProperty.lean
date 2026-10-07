module

public import ReasLib.RingTheory.FormalFiber.FieldProperty.Laws
public import ReasLib.RingTheory.Gorenstein.Ring

@[expose] public section

universe u v

namespace FieldAlgebraProperty

/-- Gorensteinness, viewed as an intrinsic property of an algebra over a field. -/
abbrev gorensteinRing : FieldAlgebraProperty.{u, v} :=
  fun _ R ↦ IsGorensteinRing R

/-- The Gorenstein field-algebra property is independent of the displayed ground field. -/
theorem gorensteinRing_iff (k : Type u) (R : Type v)
    [Field k] [CommRing R] [Algebra k R] :
    gorensteinRing k R ↔ IsGorensteinRing R := sorry

end FieldAlgebraProperty

/-- Gorensteinness satisfies the five formal-fiber permanence laws. -/
instance FieldAlgebraProperty.gorensteinRing.formalFiberLaws :
    (FieldAlgebraProperty.gorensteinRing : FieldAlgebraProperty.{u, u}).FormalFiberLaws := sorry
