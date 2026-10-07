module

public import ReasLib.Algebra.Module.DescentDatum.Effectivity

@[expose] public section

universe u

/- Compatibility bridge for effective concrete module descent data. -/
#check (@Module.DescentDatum.IsEffective :
  (R A N : Type u) → [CommRing R] → [CommRing A] → [Algebra R A] →
    [AddCommGroup N] → [Module R N] → [Module A N] →
    [IsScalarTower R A N] → [SMulCommClass R A N] →
    Module.DescentDatum R A N → Prop)
