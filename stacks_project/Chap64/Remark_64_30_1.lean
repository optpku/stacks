/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Etale.AbstractTrace

/-! # Observations on abstract trace formulas -/

public section
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open ProfiniteGrp ProfiniteGrp.ContinuousTrace
open scoped Ring
universe u v

/- Remark 64.30.1 (1). Projective curves admit the cohomological trace formula
without an additional q^n factor. -/
@[stacks 03VP] #check (AlgebraicGeometry.SchemeOverField.EtaleTrace.trace_eq_cohomology :
  ∀ {k : Type u} [Field k] [Fintype k] (X : SchemeOverField k)
    [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (η : GeometricPoint (geometricBaseChange X)),
    ∀ {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
    [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
      (smallEtalePullback f).op.HasLeftKanExtension F]
    [∀ U : X.left.Etale,
      HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [EnoughInjectives (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    (M : DiscreteModuleCat Λ
      (GeometricPoint.etaleFundamentalGroup X.left (arithmeticPoint X η)))
    [Module.Finite Λ M.obj.V],
    ∀ {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
      [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
      (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
      (T : AbstractTraceData (DegreeExtension.ofEtaleFundamentalGroup X η))
      (hT : IsAbstractTraceFormula (DegreeExtension.ofEtaleFundamentalGroup X η) T)
      (hq : T.q = Fintype.card k) (hunit : IsUnit (T.q : Λ))
      [Module.Projective Λ M.obj.V] (hcoeff : IsUnit (Nat.card Λ : k)) (n : ℕ) (hn : 0 < n),
      T.leftHandSum M n = (EtaleTrace.isPerfect_cohomology X η M hcoeff).traceNatural
        (EtaleTrace.frobenius X η M ^ n))

/- Remark 64.30.1 (2). Smooth geometrically irreducible étale K(π, 1) schemes
in the separated finite-type setting have q = card(k)^dim(X). -/
@[stacks 03VP] #check (AlgebraicGeometry.SchemeOverField.hasAbstractTraceFormula_etaleFundamentalGroup :
  ∀ {k : Type u} [Field k] [Fintype k] (X : SchemeOverField k)
    [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (η : GeometricPoint (geometricBaseChange X)),
    ∀ {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
      [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
      [Smooth X.hom] [GeometricallyIrreducible X.hom] [IsEtaleKPi1 X η],
      ∃ (d : ℕ) (T : AbstractTraceData (DegreeExtension.ofEtaleFundamentalGroup X η)),
        topologicalKrullDim X.left = (d : WithBot ℕ∞) ∧ T.q = Fintype.card k ^ d ∧
          IsAbstractTraceFormula (DegreeExtension.ofEtaleFundamentalGroup X η) T)

/- The curve specialization retains the geometric non-P¹ condition. -/
#check (AlgebraicGeometry.SchemeOverField.hasAbstractTraceFormula_etaleFundamentalGroup_curve :
  ∀ {k : Type u} [Field k] [Fintype k] (X : SchemeOverField k)
    [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (η : GeometricPoint (geometricBaseChange X)),
    ∀ {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
      [Curve X] [Smooth X.hom] [GeometricallyIrreducible X.hom]
      (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1)),
      ∃ T : AbstractTraceData (DegreeExtension.ofEtaleFundamentalGroup X η),
        T.q = Fintype.card k ∧ IsAbstractTraceFormula (DegreeExtension.ofEtaleFundamentalGroup X η) T)

/- Remark 64.30.1 (3). At fixed q the conjugacy-class multiplicities are unique. -/
@[stacks 03VP] #check (ProfiniteGrp.ContinuousTrace.AbstractTraceData.multiplicity_unique :
  ∀ (S : DegreeExtension.{u}) {T₁ T₂ : AbstractTraceData S},
    IsAbstractTraceFormula S T₁ → IsAbstractTraceFormula S T₂ →
      T₁.q = T₂.q → T₁.multiplicity = T₂.multiplicity)

/- Remark 64.30.1 (4). The numerical operation replaces q by m*q and each
degree-d multiplicity by m^d times itself. The printed invariance assertion is
false: for Γ = hatZ with trivial kernel, q = 1, one degree-one class and no
higher classes, scaling by 2 gives left side 2 and right side 4 at n = 2
with trivial ZMod 5 coefficients. The true law has divisor-dependent weights. -/
@[stacks 03VP] #check (ProfiniteGrp.ContinuousTrace.AbstractTraceData.leftHandSum_scale :
  ∀ {S : DegreeExtension.{u}} {Λ : Type v} [Ring Λ] (T : AbstractTraceData S)
    (m : ℕ) (hm : 1 ≤ m) (M : DiscreteModuleCat Λ S.middle)
    [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V] (n : ℕ),
    (T.scale m hm).leftHandSum M n =
      ∑ d ∈ n.divisors, if h : 0 < d then
        d • (m ^ d • (T.multiplicity ⟨d, h⟩).sum
          (fun c a ↦ a • conjClassTrace S M (powClass S c (n / d))))
      else 0)
