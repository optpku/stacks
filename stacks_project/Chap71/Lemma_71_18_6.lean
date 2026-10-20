module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.EffectiveCartier
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform.EffectiveCartier
import StacksCheckRecall

/-!
# Lemma 71.18.6

Blowing up an algebraic space in the product of the ideal sheaves of a closed
subspace and an effective Cartier divisor yields the same morphism over the
base as blowing up in the closed subspace, and strict transforms of modules
without sections supported on the inverse image of the divisor agree.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 71.18.6 (1): Let `S` be a scheme, `B` an algebraic space over `S`,
`Z ⊂ B` a closed subspace, and `D ⊂ B` an effective Cartier divisor. Write `Z'`
for the closed subspace cut out by `IdealSubobject.mul Z.idealSheaf D.idealSheaf`.
A blowup of `B` in `Z'` is isomorphic over `B` to a blowup of `B` in `Z`. -/
@[stacks 0867] #check (AlgebraicGeometry.AlgebraicSpace.Blowup.isoOver_mul_effectiveCartier :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (Z D : ClosedSubspace B) [IsQuasiCoherent Z.idealSheaf]
    [IsEffectiveCartierDivisor D.ι] (π : Blowup.along Z)
    (π' : Blowup.along
      (ClosedSubspace.ofQuasiCoherentIdeal
        (IdealSubobject.mul Z.idealSheaf D.idealSheaf))),
    Nonempty (Over.mk
      (Blowup.alongHom
        (ClosedSubspace.ofQuasiCoherentIdeal
          (IdealSubobject.mul Z.idealSheaf D.idealSheaf)) π') ≅ Over.mk π.hom))

/- Lemma 71.18.6 (2): Let `S` be a scheme, `B` an algebraic space over `S`,
`Z ⊂ B` a closed subspace, and `D ⊂ B` an effective Cartier divisor. Write `Z'`
for the closed subspace cut out by `IdealSubobject.mul Z.idealSheaf D.idealSheaf`.
Let `π` be a blowup of `B` in `Z`, let `f : X ⟶ B` be a morphism of algebraic
spaces, and let `F` be a quasi-coherent `𝒪_X`-module. If the subsheaf of
sections of `F` supported on `|f⁻¹D|` is zero, then the strict transform of `F`
relative to `π` with exceptional divisor `Z.inverseImageSubspace π.hom` is
isomorphic to the
strict transform relative to the same morphism with exceptional divisor
`Z'.inverseImageSubspace π.hom`, compatibly with the canonical quotient maps. -/
@[stacks 0867] #check
  (AlgebraicGeometry.AlgebraicSpace.strictTransformModule_isomorphic_mul_of_noSectionsSupportedOn :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    (Z D : ClosedSubspace B) [IsQuasiCoherent Z.idealSheaf]
    [IsEffectiveCartierDivisor D.ι] (π : Blowup.along Z)
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (h_support :
      IsZero
        (Modules.sectionsWithSupportIn
          (closedImmersionComplementι (inverseImageι f D.ι)) F)),
    ∃ e : strictTransformModule π.hom (Z.inverseImageSubspace π.hom) f F ≅
        strictTransformModule π.hom
          ((ClosedSubspace.ofQuasiCoherentIdeal
            (IdealSubobject.mul Z.idealSheaf D.idealSheaf)).inverseImageSubspace π.hom)
          f F,
      strictTransformπ π.hom (Z.inverseImageSubspace π.hom) f F ≫ e.hom =
        strictTransformπ π.hom
          ((ClosedSubspace.ofQuasiCoherentIdeal
            (IdealSubobject.mul Z.idealSheaf D.idealSheaf)).inverseImageSubspace π.hom)
          f F)
