module

public import ReasLib.RingTheory.Extension.Presentation.BaseChange
public import ReasLib.RingTheory.Extension.Presentation.RelationIdeal

/-!
# Base change of presentation relation ideals

Relation ideals and their intrinsic multiplication condition commute with
coefficient base change.
-/

@[expose] public section

open scoped TensorProduct

universe u v w t x

namespace Algebra.Presentation

variable {R : Type u} {A : Type v} {R' : Type w}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']
variable {ι : Type t} {σ : Type x}

namespace RelationIdeal

/-- A relation ideal commutes with coefficient base change. -/
theorem baseChange (P : Presentation R A ι σ) (s : Set σ) :
    (P.baseChange R').relationIdeal s =
      Ideal.map (MvPolynomial.map (algebraMap R R')) (P.relationIdeal s) := sorry

end RelationIdeal

namespace RelationCondition

/-- The intrinsic relation condition is preserved by coefficient base
change. -/
theorem baseChange
    (P : Presentation R A ι σ) {a : A} {s : Set σ}
    (h : P.relationCondition a s) :
    (P.baseChange R').relationCondition ((1 : R') ⊗ₜ[R] a) s := sorry

end RelationCondition

end Algebra.Presentation
