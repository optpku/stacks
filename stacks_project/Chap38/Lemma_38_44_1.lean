module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.Relative
public import stacks_project.Chap38.Lemma_38_43_14

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.ModuleDerived
open RingedSpace.ModuleDerived.IsPerfect
open RingedSpace.ModuleDerived.Cohomology
open RingedSpace.IdealSheaf.Eta.Derived
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLineModification

variable {X W : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace)
  (hE : RingedSpace.ModuleDerived.IsPerfect E) (P : ProjectiveSpaceOver X 1)
  (Dinf : P.scheme.IdealSheafData) [IsEffectiveCartierDivisor Dinf.subschemeι]
  (b : W ⟶ P.scheme)
  [IsGoodTripleModification Dinf
    ((RingedSpace.modulePullbackDerived P.hom.toShHom).obj E) b]

/- Lemma 38.44.1 (1): the good-triple modification is an isomorphism over the union of
the relative projective line above the finite-free locus and the divisor complement. -/
@[stacks 0F90] #check
  (AlgebraicGeometry.Scheme.IsGoodTripleModification.isIsoRestrictPullbackUnion
    E hE P.hom Dinf b :
      let U := hE.finiteFreeOpen (fun x ↦ inferInstance)
      IsIso (b ∣_ (P.hom ⁻¹ᵁ U ⊔ Dinf.openComplement)))

/- Lemma 38.44.1 (2): on the inverse image of the divisor complement, the canonical
derived eta-pullback is isomorphic to the pullback of `E` from `X`. -/
@[stacks 0F90] #check
  (AlgebraicGeometry.Scheme.IsGoodTripleModification.etaPullback_restrictOpenComplement_isIsomorphic
      E P.hom Dinf b :
    let M := (RingedSpace.modulePullbackDerived P.hom.toShHom).obj E
    let D' := Dinf.comap b
    let Q := (functor D'.toSubobject).obj
      ((RingedSpace.modulePullbackDerived b.toShHom).obj M)
    let V := b ⁻¹ᵁ Dinf.openComplement
    IsIsomorphic
      ((RingedSpace.modulePullbackDerived V.ι.toShHom).obj Q)
      ((RingedSpace.modulePullbackDerived (V.ι ≫ b ≫ P.hom).toShHom).obj E))

/- Lemma 38.44.1 (3)-(4): one finitely presented closed subscheme above the finite-free
locus has finite locally free derived eta-cohomology and the prescribed stalk ranks. -/
@[stacks 0F90] #check
  (AlgebraicGeometry.Scheme.IsGoodTripleModification.existsEtaFlatteningOfPullback
    E hE P.hom Dinf b :
    let U := hE.finiteFreeOpen (fun x ↦ inferInstance)
    let M := (RingedSpace.modulePullbackDerived P.hom.toShHom).obj E
    let D' := Dinf.comap b
    let Q := (functor D'.toSubobject).obj
      ((RingedSpace.modulePullbackDerived b.toShHom).obj M)
    ∃ J : D'.subscheme.IdealSheafData, let T := J.subscheme;
      Scheme.Hom.FinitePresentation J.subschemeι ∧
        J ≤ ((((D'.subschemeι ≫ b ≫ P.hom) ⁻¹ᵁ U).ι).ker) ∧
        finiteLocallyFreeOn
          ((RingedSpace.modulePullbackDerived
            (J.subschemeι ≫ D'.subschemeι).toShHom).obj Q) ⊤ ∧
        ∀ (n : ℤ) (t : T),
          (J.subschemeι ≫ D'.subschemeι ≫ b ≫ P.hom) t ∈ U →
            Module.rank (T.presheaf.stalk t)
                (cohomologyStalk ((RingedSpace.modulePullbackDerived
                  (J.subschemeι ≫ D'.subschemeι).toShHom).obj Q) n t) =
              Module.rank
                (X.presheaf.stalk
                  ((J.subschemeι ≫ D'.subschemeι ≫ b ≫ P.hom) t))
                (E.cohomologyStalk n
                  ((J.subschemeι ≫ D'.subschemeι ≫ b ≫ P.hom) t)))

/- Lemma 38.44.1 (5): a locally bounded termwise finite locally free representative of
`E` yields such a representative of the canonical derived eta-pullback on `W`. -/
@[stacks 0F90] #check
  (AlgebraicGeometry.Scheme.IsGoodTripleModification.etaPullback_hasLocallyBoundedFiniteLocallyFreeRepresentative_of_pullback
      E P.hom Dinf b :
    RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative E →
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((functor (Dinf.comap b).toSubobject).obj
          ((RingedSpace.modulePullbackDerived b.toShHom).obj
            ((RingedSpace.modulePullbackDerived P.hom.toShHom).obj E))))

end AlgebraicGeometry.Scheme.ProjectiveLineModification
