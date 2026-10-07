module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.AlgHom.Factorisation

/-!
# Smooth factorisations killing an ideal

This file refines a smooth factorisation by recording that its source map
kills a specified ideal.  Nilpotence and approximation hypotheses belong in
existence theorems, not in this reusable factorisation object.
-/

@[expose] public section

universe u v w

namespace AlgHom.Factorisation.Smooth

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- A smooth factorisation whose source map kills a specified ideal. -/
@[stacks 07CL "smooth factorisation killing an ideal"]
structure Killing (f : A →ₐ[R] B) (J : Ideal A) where
  /-- The underlying smooth factorisation. -/
  base : AlgHom.Factorisation.Smooth f
  /-- The specified ideal vanishes in the smooth midpoint. -/
  kills : J ≤ RingHom.ker base.fromSource.toRingHom

namespace Killing

variable {f : A →ₐ[R] B} {J : Ideal A}

/-- The smooth midpoint of an ideal-killing factorisation. -/
abbrev mid (F : Killing f J) := F.base.mid

/-- The source map of an ideal-killing factorisation. -/
noncomputable abbrev fromSource (F : Killing f J) : A →ₐ[R] F.mid :=
  F.base.fromSource

/-- The target map of an ideal-killing factorisation. -/
noncomputable abbrev toTarget (F : Killing f J) : F.mid →ₐ[R] B :=
  F.base.toTarget

/-- Attach an ideal-killing condition to a smooth factorisation. -/
def of (F : AlgHom.Factorisation.Smooth f)
    (kills : J ≤ RingHom.ker F.fromSource.toRingHom) : Killing f J :=
  { base := F
    kills := kills }

/-- Forgetting the ideal-killing condition recovers the supplied smooth
factorisation. -/
@[simp]
theorem base_of (F : AlgHom.Factorisation.Smooth f)
    {kills : J ≤ RingHom.ker F.fromSource.toRingHom} :
    (of F kills).base = F := sorry

/-- The smoothness, triangle law, and ideal-killing property carried by the
refined factorisation. -/
@[stacks 07CL "ideal-killing factorisation specification"]
theorem spec (F : Killing f J) :
    Algebra.Smooth R F.mid ∧ F.toTarget.comp F.fromSource = f ∧
      J ≤ RingHom.ker F.fromSource.toRingHom := sorry

/-- Forget the ideal-killing condition while retaining finite presentation
of the midpoint. -/
def toFinite (F : Killing f J) : AlgHom.Factorisation.Finite f :=
  F.base.toFinite

/-- Forgetting the ideal-killing condition preserves the source map. -/
@[simp]
theorem fromSource_toFinite (F : Killing f J) :
    F.toFinite.fromSource = F.fromSource := sorry

/-- Forgetting the ideal-killing condition preserves the target map. -/
@[simp]
theorem toTarget_toFinite (F : Killing f J) :
    F.toFinite.toTarget = F.toTarget := sorry

end Killing

end AlgHom.Factorisation.Smooth
