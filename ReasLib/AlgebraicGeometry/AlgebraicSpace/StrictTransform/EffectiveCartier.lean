module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.EffectiveCartier
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform

/-!
# Strict transforms and effective Cartier divisors

Multiplying a blowup center by an effective Cartier ideal preserves the strict
transform of a module without sections supported on the inverse-image divisor,
up to an isomorphism compatible with the canonical quotient maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If a quasi-coherent module has no sections supported on the inverse image of
an effective Cartier divisor, multiplying the blowup center by that divisor
preserves its strict transform up to an isomorphism commuting with the canonical
quotient maps. -/
theorem strictTransformModule_isomorphic_mul_of_noSectionsSupportedOn
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    (Z D : ClosedSubspace B) [IsQuasiCoherent Z.idealSheaf]
    [IsEffectiveCartierDivisor D.ι] (π : Blowup.along Z)
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (h_support :
      IsZero
        (Modules.sectionsWithSupportIn
          (closedImmersionComplementι (inverseImageι f D.ι)) F)) :
    ∃ e : strictTransformModule π.hom (Z.inverseImageSubspace π.hom) f F ≅
        strictTransformModule π.hom
          ((ClosedSubspace.ofQuasiCoherentIdeal
            (IdealSubobject.mul Z.idealSheaf D.idealSheaf)).inverseImageSubspace π.hom)
          f F,
      strictTransformπ π.hom (Z.inverseImageSubspace π.hom) f F ≫ e.hom =
        strictTransformπ π.hom
          ((ClosedSubspace.ofQuasiCoherentIdeal
            (IdealSubobject.mul Z.idealSheaf D.idealSheaf)).inverseImageSubspace π.hom)
          f F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
