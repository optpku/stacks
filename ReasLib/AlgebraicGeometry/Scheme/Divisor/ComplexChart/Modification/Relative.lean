/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.EtaFlattening
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.FiniteFreeLocus
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.LocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.Proper

/-!
# Good-triple modifications of pulled-back complexes

This file records relative consequences of applying a good-triple modification to the derived
pullback of a complex along a morphism of schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.ModuleDerived
open RingedSpace.ModuleDerived.IsPerfect
open RingedSpace.ModuleDerived.Cohomology
open RingedSpace.IdealSheaf.Eta.Derived
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IsGoodTripleModification

/-- A good-triple modification of a pulled-back perfect complex is an isomorphism over the
union of the inverse image of its finite-free locus and the divisor complement. -/
theorem isIsoRestrictPullbackUnion {X Y Y' : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E) (p : Y ⟶ X)
    (D : Y.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] (b : Y' ⟶ Y)
    [IsGoodTripleModification D
      ((RingedSpace.modulePullbackDerived p.toShHom).obj E) b] :
    let U := hE.finiteFreeOpen (fun x ↦ inferInstance)
    IsIso (b ∣_ (p ⁻¹ᵁ U ⊔ D.openComplement)) := sorry

/-- On the inverse image of the divisor complement, derived eta after a good-triple
modification agrees with derived pullback from the base. -/
theorem etaPullback_restrictOpenComplement_isIsomorphic {X Y Y' : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (p : Y ⟶ X)
    (D : Y.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] (b : Y' ⟶ Y)
    [IsGoodTripleModification D
      ((RingedSpace.modulePullbackDerived p.toShHom).obj E) b] :
    let M := (RingedSpace.modulePullbackDerived p.toShHom).obj E
    let D' := D.comap b
    let Q := (functor D'.toSubobject).obj
      ((RingedSpace.modulePullbackDerived b.toShHom).obj M)
    let V := b ⁻¹ᵁ D.openComplement
    IsIsomorphic
      ((RingedSpace.modulePullbackDerived V.ι.toShHom).obj Q)
      ((RingedSpace.modulePullbackDerived (V.ι ≫ b ≫ p).toShHom).obj E) := sorry

/-- A good-triple modification of a pulled-back perfect complex admits a finitely presented
closed flattening subscheme. The same subscheme contains the inverse image of the finite-free
locus, has finite locally free pulled-back eta-cohomology, and preserves all stalk ranks there. -/
theorem existsEtaFlatteningOfPullback {X Y Y' : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E) (p : Y ⟶ X)
    (D : Y.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] (b : Y' ⟶ Y)
    [IsGoodTripleModification D
      ((RingedSpace.modulePullbackDerived p.toShHom).obj E) b] :
    let U := hE.finiteFreeOpen (fun x ↦ inferInstance)
    let M := (RingedSpace.modulePullbackDerived p.toShHom).obj E
    let D' := D.comap b
    let Q := (functor D'.toSubobject).obj
      ((RingedSpace.modulePullbackDerived b.toShHom).obj M)
    ∃ J : D'.subscheme.IdealSheafData, let T := J.subscheme;
      Scheme.Hom.FinitePresentation J.subschemeι ∧
        J ≤ ((((D'.subschemeι ≫ b ≫ p) ⁻¹ᵁ U).ι).ker) ∧
        finiteLocallyFreeOn
          ((RingedSpace.modulePullbackDerived
            (J.subschemeι ≫ D'.subschemeι).toShHom).obj Q) ⊤ ∧
        ∀ (n : ℤ) (t : T),
          (J.subschemeι ≫ D'.subschemeι ≫ b ≫ p) t ∈ U →
            Module.rank (T.presheaf.stalk t)
                (cohomologyStalk ((RingedSpace.modulePullbackDerived
                  (J.subschemeι ≫ D'.subschemeι).toShHom).obj Q) n t) =
              Module.rank
                (X.presheaf.stalk
                  ((J.subschemeι ≫ D'.subschemeι ≫ b ≫ p) t))
                (E.cohomologyStalk n
                  ((J.subschemeι ≫ D'.subschemeι ≫ b ≫ p) t)) := sorry

/-- Derived pullback followed by derived eta along a good-triple modification preserves the
existence of a locally bounded finite locally free representative. -/
theorem etaPullback_hasLocallyBoundedFiniteLocallyFreeRepresentative_of_pullback
    {X Y Y' : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace) (p : Y ⟶ X)
    (D : Y.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] (b : Y' ⟶ Y)
    [IsGoodTripleModification D
      ((RingedSpace.modulePullbackDerived p.toShHom).obj E) b]
    (hrep : RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative E) :
    RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
      ((functor (D.comap b).toSubobject).obj
        ((RingedSpace.modulePullbackDerived b.toShHom).obj
          ((RingedSpace.modulePullbackDerived p.toShHom).obj E))) := sorry

end AlgebraicGeometry.Scheme.IsGoodTripleModification
