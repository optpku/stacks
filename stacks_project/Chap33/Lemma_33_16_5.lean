/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Cotangent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry TensorProduct

universe u

/- Lemma 33.16.5: when the canonical residue-field map is bijective, the cotangent
space of the distinguished fibre point is the residue-field fibre of the relative
Kähler differentials. -/
@[stacks 0B2E] #check
  (AlgebraicGeometry.Scheme.Hom.cotangentSpaceToKaehlerTensorEquiv :
    {X S : Scheme.{u}} → (f : X ⟶ S) → (x : X) →
      Function.Bijective (f.residueFieldMap x).hom →
        IsLocalRing.CotangentSpace
            (AlgebraicGeometry.Scheme.Hom.fiberStalkAt f x) ≃ₗ[X.residueField x]
          X.residueField x ⊗[X.presheaf.stalk x]
            CommRingCat.KaehlerDifferential (f.stalkMap x))

#check
  (AlgebraicGeometry.Scheme.Hom.relativeTangentSpaceToCotangentLinearDual :
    {X S : Scheme.{u}} → (f : X ⟶ S) → (x : X) →
      Function.Bijective (f.residueFieldMap x).hom →
        AlgebraicGeometry.Scheme.Hom.tangentSpaceAt f x ≃ₗ[X.residueField x]
          (IsLocalRing.CotangentSpace
              (AlgebraicGeometry.Scheme.Hom.fiberStalkAt f x) →ₗ[X.residueField x]
            X.residueField x))

#check
  (AlgebraicGeometry.Scheme.Hom.cotangentSpaceToKaehlerTensorEquivOfIsSeparable :
    {X S : Scheme.{u}} → (f : X ⟶ S) → (x : X) →
      Algebra.IsSeparable (S.residueField (f x)) (X.residueField x) →
        IsLocalRing.CotangentSpace
            (AlgebraicGeometry.Scheme.Hom.fiberStalkAt f x) ≃ₗ[X.residueField x]
          X.residueField x ⊗[X.presheaf.stalk x]
            CommRingCat.KaehlerDifferential (f.stalkMap x))

#check
  (AlgebraicGeometry.Scheme.Hom.relativeTangentSpaceLinearDualOfIsSeparable :
    {X S : Scheme.{u}} → (f : X ⟶ S) → (x : X) →
      Algebra.IsSeparable (S.residueField (f x)) (X.residueField x) →
        AlgebraicGeometry.Scheme.Hom.tangentSpaceAt f x ≃ₗ[X.residueField x]
          (IsLocalRing.CotangentSpace
              (AlgebraicGeometry.Scheme.Hom.fiberStalkAt f x) →ₗ[X.residueField x]
            X.residueField x))
