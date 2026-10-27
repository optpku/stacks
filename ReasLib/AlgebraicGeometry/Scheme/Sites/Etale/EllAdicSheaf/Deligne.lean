/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Matrix
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Stalk.Rational
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Frobenius
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.Frobenius

/-!
# Deligne conclusions for rational adic sheaves

Number-field descent, complex purity of weight zero, and compatible continuous
representations at finite places for closed-point geometric Frobenius.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.SchemeOverField
open GrothendieckTopology.Point
open IsDedekindDomain Matrix
open scoped AlgebraicGeometry NumberField Polynomial

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom] [IsNoetherian X.left]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
variable [ConnectedSpace X.left]
variable (F : ZEllSheaf X.left ℓ)

/-- A rational adic sheaf satisfies Deligne's conclusions if its closed-point
Frobenius characteristic polynomials descend to a number field and have roots
of complex norm one under every embedding, and after a finite number-field
extension they admit compatible continuous representations at every finite place
away from the characteristic, evaluated at transported geometric Frobenius. -/
def SatisfiesDeligneConclusions : Prop :=
  ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (σ : E →+* ℚ_[ℓ]),
    (∀ (x : closedPoints X.left),
        ∃ (Pₓ : Polynomial E),
          Pₓ.map σ = LinearMap.charpoly (F.geometricFrobeniusStalk x) ∧
            ∀ (τ : E →+* ℂ) (α : ℂ), (Pₓ.map τ).IsRoot α → ‖α‖ = 1) ∧
      ∃ (E' : Type u) (_ : Field E') (_ : NumberField E')
          (ι : E →+* E') (r : ℕ) (xbar : GeometricPoint X.left),
        ι.Finite ∧
          ∀ (v : HeightOneSpectrum (𝓞 E')), ringChar (𝓞 E' ⧸ v.asIdeal) ≠ p →
            ∃ (ρ : ContinuousMonoidHom (etaleFundamentalGroup X.left xbar)
                (GL (Fin r) (v.adicCompletion E'))),
              ∀ (x : closedPoints X.left)
                (ιFrob : GeometricPoint.finiteFiber (geometricPointOverClosedPoint X x) ≅
                  GeometricPoint.finiteFiber xbar),
                ∃ (Pₓ : Polynomial E),
                  Pₓ.map σ = LinearMap.charpoly (F.geometricFrobeniusStalk x) ∧
                    Pₓ.map ((NumberField.FinitePlace.embedding v).comp ι) =
                      Matrix.charpoly (ρ (etaleGeometricFrobenius X xbar x ιFrob)).val

/-- Deligne's conclusions are equivalent to number-field descent and complex
norm-one roots of closed-point Frobenius polynomials, together with compatible
continuous representations over all finite completions away from the
characteristic after a finite number-field extension. -/
theorem satisfiesDeligneConclusions_iff :
    F.SatisfiesDeligneConclusions (p := p) ↔
      ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (σ : E →+* ℚ_[ℓ]),
        (∀ (x : closedPoints X.left),
            ∃ (Pₓ : Polynomial E),
              Pₓ.map σ = LinearMap.charpoly (F.geometricFrobeniusStalk x) ∧
                ∀ (τ : E →+* ℂ) (α : ℂ), (Pₓ.map τ).IsRoot α → ‖α‖ = 1) ∧
          ∃ (E' : Type u) (_ : Field E') (_ : NumberField E')
              (ι : E →+* E') (r : ℕ) (xbar : GeometricPoint X.left),
            ι.Finite ∧
              ∀ (v : HeightOneSpectrum (𝓞 E')), ringChar (𝓞 E' ⧸ v.asIdeal) ≠ p →
                ∃ (ρ : ContinuousMonoidHom (etaleFundamentalGroup X.left xbar)
                    (GL (Fin r) (v.adicCompletion E'))),
                  ∀ (x : closedPoints X.left)
                    (ιFrob : GeometricPoint.finiteFiber (geometricPointOverClosedPoint X x) ≅
                      GeometricPoint.finiteFiber xbar),
                    ∃ (Pₓ : Polynomial E),
                      Pₓ.map σ = LinearMap.charpoly (F.geometricFrobeniusStalk x) ∧
                        Pₓ.map ((NumberField.FinitePlace.embedding v).comp ι) =
                          Matrix.charpoly (ρ (etaleGeometricFrobenius X xbar x ιFrob)).val :=
  sorry

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
