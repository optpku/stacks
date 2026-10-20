module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Rational functions represented by global sections -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The rational function represented by a global section of a scheme over `S`. -/
def sectionsToRationalFunction (T : Over S) :
    Γ(T.left, ⊤) →+* RationalFunction (ofOver T) := by
  let f : Γ(T.left, ⊤) → RationalFunction (ofOver T) :=
    fun s => (PartialMap.ofHom (ofOverMap (homOfCoord T s))).toRationalMap
  have laws : f 1 = 1 ∧
      (∀ a b, f (a * b) = f a * f b) ∧
      f 0 = 0 ∧ (∀ a b, f (a + b) = f a + f b) := by
    sorry
  exact
    { toFun := f
      map_one' := laws.1
      map_mul' := laws.2.1
      map_zero' := laws.2.2.1
      map_add' := laws.2.2.2 }

/-- Evaluation of the global-sections comparison on a section. -/
theorem sectionsToRationalFunction_apply (T : Over S) (s : Γ(T.left, ⊤)) :
    sectionsToRationalFunction T s =
      (PartialMap.ofHom (ofOverMap (homOfCoord T s))).toRationalMap :=
  rfl

/-- A global nonzerodivisor maps to a unit rational function on an integral scheme. -/
theorem isUnit_sectionsToRationalFunction (T : Over S)
    [AlgebraicGeometry.IsIntegral T.left]
    (y : nonZeroDivisors Γ(T.left, ⊤)) :
    IsUnit (sectionsToRationalFunction T y) := by
  sorry

/-- The total quotient ring of global sections maps to rational functions on an
integral scheme via the localization lift. -/
def sectionsFractionsToRationalFunction (T : Over S)
    [AlgebraicGeometry.IsIntegral T.left] :
    FractionRing Γ(T.left, ⊤) →+* RationalFunction (ofOver T) :=
  IsLocalization.lift (isUnit_sectionsToRationalFunction T)

/-- The localization comparison agrees with the global-sections comparison on
algebra-map images. -/
theorem sectionsFractionsToRationalFunction_algebraMap (T : Over S)
    [AlgebraicGeometry.IsIntegral T.left]
    (s : Γ(T.left, ⊤)) :
    sectionsFractionsToRationalFunction T (algebraMap _ _ s) =
      sectionsToRationalFunction T s := by
  exact IsLocalization.lift_eq _ _

end AlgebraicGeometry.AlgebraicSpace
