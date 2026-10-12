/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.EtaFlattening.DecompositionIdeal
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.FiniteFreeLocus
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.LocallyFree.Bounded
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.Proper

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.ModuleDerived
open CochainComplex.BerthelotOgus.Int
open RingedSpace.ModuleDerived.IsPerfect
open RingedSpace.ModuleDerived.Cohomology
open RingedSpace.IdealSheaf.Eta.Derived
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

/- Lemma 38.43.14 (1): the effective Cartier divisor and perfect complex admit a proper
good-triple modification. -/
@[stacks 0F9Y] #check
  (AlgebraicGeometry.Scheme.existsProperGoodTripleModification :
    (X : Scheme.{u}) → (D : X.IdealSheafData) →
      [IsEffectiveCartierDivisor D.subschemeι] →
      (M : RingedSpace.ModuleDerived X.toRingedSpace) →
      RingedSpace.ModuleDerived.IsPerfect M →
      ∃ (X' : Scheme.{u}) (b : X' ⟶ X),
        AlgebraicGeometry.Scheme.IsGoodTripleModification D M b ∧ IsProper b)

/- Lemma 38.43.14 (2): a good-triple modification is an isomorphism over the complement
of the divisor. -/
@[stacks 0F9Y] #check
  (AlgebraicGeometry.Scheme.IsGoodTripleModification.instIsIsoRestrictOpenComplement :
    ∀ {X X' : Scheme.{u}} {D : X.IdealSheafData}
      {M : RingedSpace.ModuleDerived X.toRingedSpace} {b : X' ⟶ X},
      [AlgebraicGeometry.Scheme.IsGoodTripleModification D M b] →
        IsIso (b ∣_ D.openComplement))

/- Lemma 38.43.14 (3): the modification is an isomorphism over the maximal open where the
cohomology of the original perfect complex is finite locally free. -/
@[stacks 0F9Y] #check
  (AlgebraicGeometry.Scheme.IsGoodTripleModification.isIsoRestrictFiniteFreeOpen :
    {X X' : Scheme.{u}} → (D : X.IdealSheafData) →
      [IsEffectiveCartierDivisor D.subschemeι] →
      (M : RingedSpace.ModuleDerived X.toRingedSpace) →
      (hM : RingedSpace.ModuleDerived.IsPerfect M) → (b : X' ⟶ X) →
      [AlgebraicGeometry.Scheme.IsGoodTripleModification D M b] →
        IsIso (b ∣_ hM.finiteFreeOpen (fun x ↦ inferInstance)))

/- Lemma 38.43.14 (4): the inverse-image divisor on the modification is effective Cartier. -/
@[stacks 0F9Y] #check
  (AlgebraicGeometry.Scheme.IsGoodTripleModification.instIsEffectiveCartierDivisor :
    ∀ {X X' : Scheme.{u}} {D : X.IdealSheafData}
      {M : RingedSpace.ModuleDerived X.toRingedSpace} {b : X' ⟶ X},
      [AlgebraicGeometry.Scheme.IsGoodTripleModification D M b] →
        IsEffectiveCartierDivisor (D.comap b).subschemeι)

/- Lemma 38.43.14 (5): the canonical derived eta-object on the modification is perfect. -/
@[stacks 0F9Y] #check
  (AlgebraicGeometry.Scheme.IsGoodTripleModification.etaPullback_isPerfect :
    {X X' : Scheme.{u}} → (D : X.IdealSheafData) →
      [IsEffectiveCartierDivisor D.subschemeι] →
      (M : RingedSpace.ModuleDerived X.toRingedSpace) →
      RingedSpace.ModuleDerived.IsPerfect M → (b : X' ⟶ X) →
      [AlgebraicGeometry.Scheme.IsGoodTripleModification D M b] →
        RingedSpace.ModuleDerived.IsPerfect
          ((functor (D.comap b).toSubobject).obj
            ((RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M)))

/- Lemma 38.43.14 (6): on a source affine chart, the modification is the blowup in the
product of the degreewise determinantal ideals. -/
@[stacks 0F9Y] #check
  (AlgebraicGeometry.Scheme.IsGoodTripleModification.isBlowup_restrict_affineChart :
    {X X' : Scheme.{u}} → (D : X.IdealSheafData) →
      [IsEffectiveCartierDivisor D.subschemeι] →
      (M : RingedSpace.ModuleDerived X.toRingedSpace) → (b : X' ⟶ X) →
      [AlgebraicGeometry.Scheme.IsGoodTripleModification D M b] →
      (C : AlgebraicGeometry.Scheme.DivisorComplexChart D M) →
        AlgebraicGeometry.IsBlowup (b ∣_ C.U) C.productCenter)

/- Lemma 38.43.14 (7): on a principal target chart, derived sections of the canonical
derived eta-object are isomorphic to the ring-level derived eta of the chart model. -/
@[stacks 0F9Y] #check
  (AlgebraicGeometry.Scheme.IsGoodTripleModification.etaPullback_affineChart_isIsomorphic :
    {X X' : Scheme.{u}} → (D : X.IdealSheafData) →
      [IsEffectiveCartierDivisor D.subschemeι] →
      (M : RingedSpace.ModuleDerived X.toRingedSpace) →
      RingedSpace.ModuleDerived.IsPerfect M → (b : X' ⟶ X) →
      [AlgebraicGeometry.Scheme.IsGoodTripleModification D M b] →
      (C : AlgebraicGeometry.Scheme.DivisorComplexChart (D.comap b)
        ((RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M)) →
      (∀ i : ℤ, (C.ideal i).IsPrincipal) →
        IsIsomorphic
          ((Derived.functor
            ⟨C.generator, C.regular⟩).obj (DerivedCategory.Q.obj C.model))
          ((RingedSpace.moduleDerivedSectionsAtOpen X'.toRingedSpace C.U).obj
            ((functor (D.comap b).toSubobject).obj
              ((RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M))))

/- Lemma 38.43.14 (8): one finitely presented flattening subscheme has finite locally free
derived eta-cohomology with the prescribed ranks, and on every principal affine chart its
ideal is the Berthelot–Ogus decomposition ideal. -/
@[stacks 0F9Y] #check
  (AlgebraicGeometry.Scheme.IsGoodTripleModification.existsEtaFlatteningWithAffineIdeal :
    {X X' : Scheme.{u}} → (D : X.IdealSheafData) →
      [IsEffectiveCartierDivisor D.subschemeι] →
      (M : RingedSpace.ModuleDerived X.toRingedSpace) →
      (hM : RingedSpace.ModuleDerived.IsPerfect M) → (b : X' ⟶ X) →
      [AlgebraicGeometry.Scheme.IsGoodTripleModification D M b] →
      let D' := D.comap b
      let M' := (RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M
      let Q := (functor D'.toSubobject).obj M'
      let W := hM.finiteFreeOpen (fun x ↦ inferInstance)
      ∃ J : D'.subscheme.IdealSheafData, let T := J.subscheme;
        Scheme.Hom.FinitePresentation J.subschemeι ∧
          J ≤ (((D'.subschemeι ≫ b) ⁻¹ᵁ W).ι).ker ∧
          finiteLocallyFreeOn
            ((RingedSpace.modulePullbackDerived
              (J.subschemeι ≫ D'.subschemeι).toShHom).obj Q) ⊤ ∧
          (∀ (n : ℤ) (t : T),
            (J.subschemeι ≫ D'.subschemeι ≫ b) t ∈ W →
              Module.rank (T.presheaf.stalk t)
                  (cohomologyStalk ((RingedSpace.modulePullbackDerived
                    (J.subschemeι ≫ D'.subschemeι).toShHom).obj Q) n t) =
                Module.rank
                  (X.presheaf.stalk ((J.subschemeι ≫ D'.subschemeι ≫ b) t))
                  (M.cohomologyStalk n ((J.subschemeι ≫ D'.subschemeι ≫ b) t))) ∧
          ∀ (C : AlgebraicGeometry.Scheme.DivisorComplexChart D' M'),
            (∀ i : ℤ, (C.ideal i).IsPrincipal) →
              C.restrictIdeal J = C.decompositionIdeal)

/- Lemma 38.43.14 (9): if `M` has a locally bounded termwise finite locally free
representative, then its canonical derived eta-pullback has a globally bounded termwise finite
locally free representative. -/
@[stacks 0F9Y] #check
  (AlgebraicGeometry.Scheme.IsGoodTripleModification.existsBoundedEtaPullbackRepresentative :
    {X X' : Scheme.{u}} → (D : X.IdealSheafData) →
      [IsEffectiveCartierDivisor D.subschemeι] →
      (M : RingedSpace.ModuleDerived X.toRingedSpace) →
      RingedSpace.ModuleDerived.IsPerfect M → (b : X' ⟶ X) →
      [AlgebraicGeometry.Scheme.IsGoodTripleModification D M b] →
      (∃ P : CochainComplex X.toRingedSpace.Modules ℤ,
        IsIsomorphic (DerivedCategory.Q.obj P) M ∧
          RingedSpace.CochainComplex.IsLocallyBoundedAbove P ∧
          RingedSpace.CochainComplex.IsLocallyBoundedBelow P ∧
          ∀ i : ℤ, SheafOfModules.IsFiniteLocallyFree (P.X i)) →
        ∃ Q : CochainComplex X'.toRingedSpace.Modules ℤ,
          IsIsomorphic (DerivedCategory.Q.obj Q)
              ((functor (D.comap b).toSubobject).obj
                ((RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M)) ∧
            _root_.CochainComplex.bounded X'.toRingedSpace.Modules Q ∧
            ∀ i : ℤ, SheafOfModules.IsFiniteLocallyFree (Q.X i))
