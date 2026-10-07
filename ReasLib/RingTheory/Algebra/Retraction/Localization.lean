module

public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.RingTheory.Algebra.Retraction

/-!
# Principal localization of retract extensions

This leaf owns the canonical map between corresponding principal
localizations of the source and carrier of a retract extension.
-/

@[expose] public section

noncomputable section

universe u v w

namespace Algebra.RetractExtension

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]

/-- The canonical map between principal localizations induced by a retract extension. -/
@[stacks 07CE "localized retract-extension map"]
noncomputable abbrev awayMap (E : RetractExtension.{u, v, w} R A) (a : A) :
    Localization.Away a →ₐ[R]
      Localization.Away (algebraMap A E.carrier a) :=
  Localization.awayMapₐ (IsScalarTower.toAlgHom R A E.carrier) a

end Algebra.RetractExtension
