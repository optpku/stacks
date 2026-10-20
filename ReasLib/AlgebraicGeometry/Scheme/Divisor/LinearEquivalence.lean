module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Picard
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Two effective Cartier divisors are linearly equivalent when their associated invertible
modules are isomorphic. -/
def linearlyEquivalent (X : Scheme.{u}) (D E : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    [IsEffectiveCartierDivisor E.subschemeι] : Prop :=
  Nonempty (D.associatedSheaf ≅ E.associatedSheaf)

/-- Linear equivalence unfolds to isomorphism of the associated invertible modules. -/
theorem linearlyEquivalent_def (X : Scheme.{u}) (D E : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    [IsEffectiveCartierDivisor E.subschemeι] :
    linearlyEquivalent X D E ↔ Nonempty (D.associatedSheaf ≅ E.associatedSheaf) := sorry

/-- Every effective Cartier divisor is linearly equivalent to itself. -/
theorem linearlyEquivalent_refl (X : Scheme.{u}) (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    linearlyEquivalent X D D := sorry

/-- Linear equivalence of effective Cartier divisors is symmetric. -/
theorem linearlyEquivalent_symm (X : Scheme.{u}) (D E : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    [IsEffectiveCartierDivisor E.subschemeι] :
    linearlyEquivalent X D E → linearlyEquivalent X E D := sorry

/-- Linear equivalence of effective Cartier divisors is transitive. -/
theorem linearlyEquivalent_trans (X : Scheme.{u}) (D E F : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    [IsEffectiveCartierDivisor E.subschemeι]
    [IsEffectiveCartierDivisor F.subschemeι] :
    linearlyEquivalent X D E → linearlyEquivalent X E F → linearlyEquivalent X D F := sorry

/-- On a smooth projective curve, linear equivalence is equality of the associated Picard classes. -/
theorem linearlyEquivalent_iff_picardClass_eq
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D E : X.left.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    [IsEffectiveCartierDivisor E.subschemeι] :
    linearlyEquivalent X.left D E ↔
      Scheme.Modules.picardClass D.associatedSheaf =
        Scheme.Modules.picardClass E.associatedSheaf := sorry

/-- On a smooth projective curve, linear equivalence is equality of the associated Weil divisor
class-group images. -/
theorem linearlyEquivalent_iff_weilDivisorClass_eq
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D E : X.left.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    [IsEffectiveCartierDivisor E.subschemeι] :
    let toCl := @Scheme.picardToWeilDivisorClassGroup X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom) inferInstance
    linearlyEquivalent X.left D E ↔
      toCl (Scheme.Modules.picardClass D.associatedSheaf) =
        toCl (Scheme.Modules.picardClass E.associatedSheaf) := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
