/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

namespace DivisorComplexChart

/-- The finite product of the degreewise determinantal ideals attached to an affine
divisor-complex chart. -/
noncomputable def productIdeal {X : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} (C : DivisorComplexChart D M) :
    Ideal Γ(X, C.U) :=
  ∏ᶠ i : ℤ,
    @CochainComplex.BerthelotOgus.Int.etaDeterminantalIdeal
      _ _ C.generator C.model i
        (@HomologicalComplex.IsTermwiseFiniteFree.out _ _ _ _ C.model C.finiteFree i).2
        (@HomologicalComplex.IsTermwiseFiniteFree.out
          _ _ _ _ C.model C.finiteFree (i + 1)).1
        (@HomologicalComplex.IsTermwiseFiniteFree.out
          _ _ _ _ C.model C.finiteFree (i + 1)).2

/-- Only finitely many degreewise determinantal ideals of an affine divisor-complex chart
differ from the unit ideal. -/
theorem ideal_hasFiniteMulSupport {X : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} (C : DivisorComplexChart D M) :
    Function.HasFiniteMulSupport fun i : ℤ ↦ C.ideal i := sorry

/-- The product ideal is the finitary product of all degreewise determinantal ideals. -/
theorem productIdeal_def {X : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} (C : DivisorComplexChart D M) :
    C.productIdeal = ∏ᶠ i : ℤ, C.ideal i := sorry

/-- The ideal-sheaf center on the affine chart obtained by transporting the product ideal to
the global sections of the restricted scheme. -/
noncomputable def productCenter {X : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} (C : DivisorComplexChart D M) :
    (C.U : X.Opens).toScheme.IdealSheafData :=
  IdealSheafData.ofIdealTop
    (Ideal.map (C.U : X.Opens).topIso.inv.hom C.productIdeal)

/-- On global sections, the chart center is the product ideal transported through
`C.U.topIso`. -/
theorem productCenter_ideal {X : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} (C : DivisorComplexChart D M) :
    IdealSheafData.equivOfIsAffine C.productCenter =
      Ideal.map (C.U : X.Opens).topIso.inv.hom C.productIdeal := sorry

end DivisorComplexChart

/-- A morphism is a good-triple modification when the divisor pullback is defined, the derived
pullback forms a good triple, and every other morphism with these properties factors uniquely
through it. -/
class IsGoodTripleModification {X X' : Scheme.{u}} (D : X.IdealSheafData)
    (M : outParam (RingedSpace.ModuleDerived X.toRingedSpace)) (b : X' ⟶ X) : Prop where
  /-- The inverse image of the divisor along the modification is defined. -/
  pullbackDefined : D.pullbackDefined b
  /-- The pulled-back divisor and derived module form a good triple. -/
  isGoodTriple :
    IsGoodTriple (D.comap b)
      ((RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M)
  /-- Every morphism whose pullbacks form a good triple factors uniquely through the
  modification. -/
  lift_unique {Y : Scheme.{u}} (h : Y ⟶ X) (h_pullback : D.pullbackDefined h)
      (h_good : IsGoodTriple (D.comap h)
        ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M)) :
    ExistsUnique fun c : Y ⟶ X' ↦ c ≫ b = h

/-- The defining conditions for a good-triple modification. -/
theorem isGoodTripleModification_iff {X X' : Scheme.{u}} (D : X.IdealSheafData)
    (M : RingedSpace.ModuleDerived X.toRingedSpace) (b : X' ⟶ X) :
    IsGoodTripleModification D M b ↔
      D.pullbackDefined b ∧
        IsGoodTriple (D.comap b)
          ((RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M) ∧
        ∀ {Y : Scheme.{u}} (h : Y ⟶ X), D.pullbackDefined h →
          IsGoodTriple (D.comap h)
            ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M) →
          ExistsUnique fun c : Y ⟶ X' ↦ c ≫ b = h := sorry

namespace IsGoodTripleModification

/-- A good-triple modification makes the pulled-back divisor effective Cartier. -/
theorem toIsEffectiveCartierDivisor {X X' : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} {b : X' ⟶ X}
    [h : IsGoodTripleModification D M b] :
    AlgebraicGeometry.IsEffectiveCartierDivisor (D.comap b).subschemeι := sorry

/-- The pulled-back divisor of a good-triple modification is canonically effective Cartier. -/
instance instIsEffectiveCartierDivisor {X X' : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} {b : X' ⟶ X}
    [IsGoodTripleModification D M b] :
    AlgebraicGeometry.IsEffectiveCartierDivisor (D.comap b).subschemeι :=
  toIsEffectiveCartierDivisor

/-- The universal property supplies the unique factorization of any competing good-triple
morphism. -/
theorem existsUnique_lift {X X' Y : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} {b : X' ⟶ X}
    [h_b : IsGoodTripleModification D M b] (h : Y ⟶ X)
    (h_pullback : D.pullbackDefined h)
    (h_good : IsGoodTriple (D.comap h)
      ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M)) :
    ExistsUnique fun c : Y ⟶ X' ↦ c ≫ b = h :=
  h_b.lift_unique h h_pullback h_good

/-- There is a unique isomorphism over the common target between two good-triple
modifications. -/
theorem existsUnique_iso {X X₁ X₂ : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} {b₁ : X₁ ⟶ X} {b₂ : X₂ ⟶ X}
    [IsGoodTripleModification D M b₁] [IsGoodTripleModification D M b₂] :
    ExistsUnique fun e : X₁ ≅ X₂ ↦ e.hom ≫ b₂ = b₁ := sorry

/-- Restricting a good-triple modification to an affine divisor-complex chart is the blowup in
the chart's product center. -/
theorem isBlowup_restrict_affineChart {X X' : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace) (b : X' ⟶ X)
    [IsGoodTripleModification D M b] (C : DivisorComplexChart D M) :
    IsBlowup (b ∣_ C.U) C.productCenter := sorry

end IsGoodTripleModification

/-- An effective Cartier divisor and a perfect derived module admit a universal modification
on which their pullbacks form a good triple. -/
theorem exists_isGoodTripleModification (X : Scheme.{u}) (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X), IsGoodTripleModification D M b := sorry

namespace IsGoodTripleModification

/-- Over a quasi-compact open, a good-triple modification is an admissible blowup away from
the restricted divisor. -/
theorem isAdmissibleBlowup_restrict {X X' : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (b : X' ⟶ X)
    [IsGoodTripleModification D M b] (W : X.Opens) [QuasiCompact W.ι] :
    IsAdmissibleBlowup (D.comap W.ι).openComplement (b ∣_ W) := sorry

end IsGoodTripleModification

end AlgebraicGeometry.Scheme
