/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Length
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealSubobject.Kernel
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.IdealStalk

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The stalk ideal of closed-subscheme data at a point, expressed through the canonical
closed-immersion kernel ideal. -/
noncomputable abbrev pointIntersectionStalkIdeal
    (Y : X.IdealSheafData) (p : X) : Ideal (X.presheaf.stalk p) :=
  RingedSpace.idealSheafStalkIdeal
    (LocallyRingedSpace.closedImmersionIdealSubobject Y.subschemeι.toLRSHom) p

/-- The pointwise intersection multiplicity of two closed subschemes is the `ℕ∞`-valued length
of the ambient local ring modulo the sum of their stalk ideals. -/
noncomputable def pointIntersectionMultiplicity
    (Y Z : X.IdealSheafData) (p : X) : ℕ∞ :=
  (Module.length (X.presheaf.stalk p)
    (X.presheaf.stalk p ⧸
      (pointIntersectionStalkIdeal Y p ⊔ pointIntersectionStalkIdeal Z p)))

/-- The pointwise intersection multiplicity unfolds to its local quotient-length formula. -/
theorem pointIntersectionMultiplicity_def (Y Z : X.IdealSheafData) (p : X) :
    Y.pointIntersectionMultiplicity Z p =
      (Module.length (X.presheaf.stalk p)
        (X.presheaf.stalk p ⧸
          (pointIntersectionStalkIdeal Y p ⊔ pointIntersectionStalkIdeal Z p))) := sorry

/-- A finite pointwise intersection multiplicity, specialized to a natural number using the
explicit proof that its quotient length is not infinite. -/
noncomputable def pointIntersectionMultiplicityNat
    (Y Z : X.IdealSheafData) (p : X)
    (hfinite : Y.pointIntersectionMultiplicity Z p ≠ ⊤) : ℕ :=
  WithTop.untop (Y.pointIntersectionMultiplicity Z p) hfinite

/-- The natural-valued finite specialization coerces back to pointwise intersection
multiplicity. -/
theorem coe_pointIntersectionMultiplicityNat
    (Y Z : X.IdealSheafData) (p : X)
    (hfinite : Y.pointIntersectionMultiplicity Z p ≠ ⊤) :
    (Y.pointIntersectionMultiplicityNat Z p hfinite : ℕ∞) =
      Y.pointIntersectionMultiplicity Z p := sorry

/-- Pointwise intersection multiplicity is finite exactly when its quotient module has finite
length. -/
theorem pointIntersectionMultiplicity_ne_top_iff
    (Y Z : X.IdealSheafData) (p : X) :
    Y.pointIntersectionMultiplicity Z p ≠ ⊤ ↔
      IsFiniteLength (X.presheaf.stalk p)
        (X.presheaf.stalk p ⧸
          (pointIntersectionStalkIdeal Y p ⊔ pointIntersectionStalkIdeal Z p)) := sorry

/-- Pointwise intersection multiplicity is symmetric in the two closed subschemes. -/
theorem pointIntersectionMultiplicity_comm (Y Z : X.IdealSheafData) (p : X) :
    Y.pointIntersectionMultiplicity Z p = Z.pointIntersectionMultiplicity Y p := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
