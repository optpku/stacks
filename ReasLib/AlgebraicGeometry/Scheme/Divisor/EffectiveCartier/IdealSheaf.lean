module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.AssociatedSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject

/-!
# Ideal-sheaf presentations of effective Cartier divisors

This leaf relates the canonical closed-immersion predicate for an effective
Cartier divisor to the ideal-sheaf models used by divisor computations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The canonical effective-Cartier condition on `D.subschemeι` is equivalent
to invertibility of the kernel ideal sheaf defining `D`. -/
theorem isEffectiveCartierDivisor_iff_hasInvertibleIdealSheaf
    (D : X.IdealSheafData) :
    AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι ↔
      Scheme.Modules.Invertible
        (kernel (SheafOfModules.unitToPushforwardObjUnit
          D.subschemeι.toRingCatSheafHom)) := sorry

/-- The ideal subobject of an effective Cartier divisor is tensor-invertible for the canonical
scheme-module tensor product. -/
theorem effectiveCartierIdealInvertible
    (D : X.IdealSheafData) (hD : AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι) :
    Scheme.Modules.Invertible
      (Subobject.underlying.obj D.toSubobject) := sorry

/-- The ideal sheaf of an effective Cartier divisor is tensor-invertible. -/
instance instInvertibleToSubobject (D : X.IdealSheafData)
    [hD : AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι] :
    Scheme.Modules.Invertible D.toSubobject.toModule :=
  effectiveCartierIdealInvertible D hD

/-- Effective-Cartier invertibility supplies the `Fact` interface used by APIs stated directly
with tensor-right equivalences. -/
theorem effectiveCartierIdealFact
    (D : X.IdealSheafData) (hD : AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι) :
    Fact
      (Functor.IsEquivalence
        (tensorRight
          (Subobject.underlying.obj D.toSubobject))) := sorry

/-- The sheaf associated to an effective Cartier divisor is the internal-Hom dual of its
ideal sheaf. -/
noncomputable abbrev associatedSheaf
    (D : X.IdealSheafData) [hD : AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι] :
    SheafOfModules X.ringCatSheaf :=
  @Scheme.effectiveCartierDivisorAssociatedSheaf X inferInstance D.toSubobject
    (effectiveCartierIdealFact D hD)

/-- The canonical global section of the sheaf associated to an effective Cartier divisor is
induced by the inclusion of its ideal sheaf into the structure sheaf. -/
noncomputable abbrev canonicalSection
    (D : X.IdealSheafData) [hD : AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι] :
    (associatedSheaf D).sections :=
  @Scheme.effectiveCartierDivisorCanonicalSection X inferInstance D.toSubobject
    (effectiveCartierIdealFact D hD)

/-- The negative sheaf of an effective Cartier divisor is its ideal sheaf. -/
noncomputable abbrev negSheaf
    (D : X.IdealSheafData) [hD : AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι] :
    SheafOfModules X.ringCatSheaf :=
  @Scheme.effectiveCartierDivisorNegSheaf X D.toSubobject
    (effectiveCartierIdealFact D hD)

/-- The sheaf associated to the difference of two effective Cartier divisors is the tensor
product of the positive associated sheaf with the negative sheaf. -/
noncomputable abbrev differenceSheaf
    (D D' : X.IdealSheafData)
    [hD : AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    [hD' : AlgebraicGeometry.IsEffectiveCartierDivisor D'.subschemeι] :
    SheafOfModules X.ringCatSheaf :=
  @Scheme.effectiveCartierDivisorDifferenceSheaf X inferInstance D.toSubobject D'.toSubobject
    (effectiveCartierIdealFact D hD) (effectiveCartierIdealFact D' hD')

end AlgebraicGeometry.Scheme.IdealSheafData
