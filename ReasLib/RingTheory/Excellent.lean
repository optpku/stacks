module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.Universally
public import ReasLib.RingTheory.Regular.GRing
public import ReasLib.RingTheory.Regular.JRing

@[expose] public section

/-!
# Excellent rings

Quasi-excellence and excellence are component owners.  Explicit component constructors avoid
installing temporary instances merely to assemble these propositions.

@stack 07QT
-/

universe u v

variable (R : Type u) [CommRing R]

/-- A ring is quasi-excellent when it is a `G`-ring and `J-2`. -/
@[stacks 07QT "(1), quasi-excellent rings"]
class IsQuasiExcellentRing : Prop extends IsGRing R, IsJ2Ring.{u, v} R

/-- A ring is excellent when it is quasi-excellent and universally catenary. -/
@[stacks 07QT "(2), excellent rings"]
class IsExcellentRing : Prop extends IsQuasiExcellentRing.{u, v} R,
    UniversallyCatenaryRing.{u, v} R

namespace IsQuasiExcellentRing

/-- Assemble quasi-excellence from its two mathematical components. -/
@[stacks 07QT "quasi-excellence component constructor"]
theorem ofComponents {R : Type u} [CommRing R]
    (hG : IsGRing R) (hJ2 : IsJ2Ring.{u, v} R) :
    IsQuasiExcellentRing.{u, v} R := sorry

end IsQuasiExcellentRing

/-- Quasi-excellence is exactly the conjunction of the `G`-ring and `J-2` conditions. -/
@[stacks 07QT "quasi-excellence component criterion"]
theorem isQuasiExcellentRing_iff {R : Type u} [CommRing R] :
    IsQuasiExcellentRing.{u, v} R ↔ IsGRing R ∧ IsJ2Ring.{u, v} R := sorry

namespace IsExcellentRing

/-- Assemble excellence from quasi-excellence and universal catenarity. -/
@[stacks 07QT "excellence component constructor"]
theorem ofComponents {R : Type u} [CommRing R]
    (hQE : IsQuasiExcellentRing.{u, v} R) (hUC : UniversallyCatenaryRing.{u, v} R) :
    IsExcellentRing.{u, v} R := sorry

end IsExcellentRing

/-- Excellence is exactly quasi-excellence together with universal catenarity. -/
@[stacks 07QT "excellence component criterion"]
theorem isExcellentRing_iff {R : Type u} [CommRing R] :
    IsExcellentRing.{u, v} R ↔
      IsQuasiExcellentRing.{u, v} R ∧ UniversallyCatenaryRing.{u, v} R := sorry
