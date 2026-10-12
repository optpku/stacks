/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.Artinian.PowerRefinement

@[expose] public section

/-!
# Artinian power refinements of algebra homomorphisms

This file lifts the presentation-independent ring-homomorphism refinement to
an algebra-compatible diagram.  The ring maps and their mathematical
properties remain owned by `RingHom.Artinian.PowerRefinement`; this wrapper
stores only the additional scalar structure and its source compatibility.
-/

universe u v w x

namespace AlgHom.Artinian

/-- An algebra-compatible lift of a ring-homomorphism Artinian power
refinement.  Only the additional scalar structure and compatibility are
stored here. -/
@[stacks 07FI "algebra-compatible local Artinian power refinement datum"]
structure PowerRefinement
    {k : Type u} {D : Type v} {T : Type w}
    [CommRing k] [CommRing D] [CommRing T] [Algebra k D] [Algebra k T]
    (f : D →ₐ[k] T) (t : T) where
  /-- The presentation-independent underlying ring-map refinement. -/
  toRingHom : RingHom.Artinian.PowerRefinement.{v, w, x} f.toRingHom t
  /-- The base-algebra structure on the intermediate algebra. -/
  instAlgebra : Algebra k toRingHom.mid
  /-- The source ring map respects the chosen base-algebra structure. -/
  fromSource_commutes : ∀ r : k,
    toRingHom.fromSource (algebraMap k D r) =
      algebraMap k toRingHom.mid r

attribute [instance] PowerRefinement.instAlgebra
attribute [stacks 07FI "underlying ring-homomorphism power refinement"]
  PowerRefinement.toRingHom

namespace PowerRefinement

variable {k : Type u} {D : Type v} {T : Type w}
variable [CommRing k] [CommRing D] [CommRing T] [Algebra k D] [Algebra k T]
variable {f : D →ₐ[k] T} {t : T}

/-- Build an algebra-compatible refinement from its underlying ring-map
refinement and scalar compatibility. -/
def of
    (P : RingHom.Artinian.PowerRefinement.{v, w, x} f.toRingHom t)
    [Algebra k P.mid]
    (hscalar : ∀ r : k,
      P.fromSource (algebraMap k D r) = algebraMap k P.mid r) :
    PowerRefinement.{u, v, w, x} f t where
  toRingHom := P
  instAlgebra := inferInstance
  fromSource_commutes := hscalar

/-- The positive exponent selected by the underlying ring-map refinement. -/
abbrev exponent (P : PowerRefinement.{u, v, w, x} f t) : ℕ+ :=
  P.toRingHom.exponent

/-- The intermediate Artinian local algebra of a scalar-compatible
refinement. -/
abbrev mid (P : PowerRefinement.{u, v, w, x} f t) :=
  P.toRingHom.mid

/-- The source algebra homomorphism of a scalar-compatible refinement. -/
def fromSource (P : PowerRefinement.{u, v, w, x} f t) : D →ₐ[k] P.mid where
  toRingHom := P.toRingHom.fromSource
  commutes' := P.fromSource_commutes

namespace fromSource

/-- The source algebra map is local when the original source is Artinian
local.  Typeclass search obtains the same fact from the underlying ring-map
refinement; this named theorem is only the algebra-facing bridge. -/
theorem isLocal [IsArtinianRing D] [IsLocalRing D]
    (P : PowerRefinement.{u, v, w, x} f t) :
    IsLocalHom P.fromSource.toRingHom := sorry

end fromSource

/-- The underlying target ring map respects the scalar structure forced by
the source compatibility and factorization equation. -/
theorem toTarget_commutes (P : PowerRefinement.{u, v, w, x} f t) (r : k) :
    P.toRingHom.toTarget (algebraMap k P.mid r) = algebraMap k T r := sorry

/-- The target algebra homomorphism of a scalar-compatible refinement. -/
def toTarget (P : PowerRefinement.{u, v, w, x} f t) : P.mid →ₐ[k] T where
  toRingHom := P.toRingHom.toTarget
  commutes' := P.toTarget_commutes

namespace toTarget

/-- The target algebra map is local whenever the target is nontrivial. -/
theorem isLocal [Nontrivial T]
    (P : PowerRefinement.{u, v, w, x} f t) :
    IsLocalHom P.toTarget.toRingHom := sorry

end toTarget

/-- The algebra maps of a refinement factor the original algebra map. -/
theorem factor (P : PowerRefinement.{u, v, w, x} f t) :
    P.toTarget.comp P.fromSource = f := sorry

/-- The source map of a scalar-compatible refinement is essentially smooth. -/
theorem smooth (P : PowerRefinement.{u, v, w, x} f t) :
    P.fromSource.toRingHom.EssSmooth := sorry

/-- The target map of a scalar-compatible refinement is flat. -/
theorem flat (P : PowerRefinement.{u, v, w, x} f t) :
    P.toTarget.toRingHom.Flat := sorry

/-- The selected target-element power lies in the image of the target map. -/
theorem power_mem (P : PowerRefinement.{u, v, w, x} f t) :
    RingHom.PowerImage.InRange P.toTarget.toRingHom t P.exponent := sorry

/-- The conditions stored by an algebra-compatible Artinian power
refinement. -/
@[stacks 07FI "algebra-compatible local Artinian power refinement specification"]
theorem spec (P : PowerRefinement.{u, v, w, x} f t) :
    IsArtinianRing P.mid ∧
      IsLocalRing P.mid ∧
      P.toTarget.comp P.fromSource = f ∧
      P.fromSource.toRingHom.EssSmooth ∧
      P.toTarget.toRingHom.Flat ∧
      RingHom.PowerImage.InRange P.toTarget.toRingHom t P.exponent := sorry

/-- Both maps of an algebra power refinement are local under the minimal
endpoint hypotheses. -/
theorem local_spec [IsArtinianRing D] [IsLocalRing D] [Nontrivial T]
    (P : PowerRefinement.{u, v, w, x} f t) :
    IsLocalHom P.fromSource.toRingHom ∧ IsLocalHom P.toTarget.toRingHom := sorry

/-- The scalar lift preserves the selected exponent. -/
@[simp]
theorem toRingHom_exponent (P : PowerRefinement.{u, v, w, x} f t) :
    P.toRingHom.exponent = P.exponent := sorry

/-- The source algebra map has the source ring map of the underlying
refinement. -/
@[simp]
theorem toRingHom_fromSource (P : PowerRefinement.{u, v, w, x} f t) :
    P.toRingHom.fromSource = P.fromSource.toRingHom := sorry

/-- The target algebra map has the target ring map of the underlying
refinement. -/
@[simp]
theorem toRingHom_toTarget (P : PowerRefinement.{u, v, w, x} f t) :
    P.toRingHom.toTarget = P.toTarget.toRingHom := sorry

/-- A flat algebra map of Artinian local rings in positive prime
characteristic has an algebra-compatible power refinement for every target
element. -/
@[stacks 07FI "existence of an algebra-compatible local Artinian power refinement"]
theorem nonempty [IsArtinianRing D] [IsLocalRing D]
    [IsArtinianRing T] [IsLocalRing T]
    {p : ℕ} [Fact p.Prime] [CharP D p]
    (f : D →ₐ[k] T) (hflat : f.toRingHom.Flat) (t : T) :
    Nonempty (PowerRefinement.{u, v, w, max v w} f t) := sorry

end PowerRefinement

end AlgHom.Artinian
