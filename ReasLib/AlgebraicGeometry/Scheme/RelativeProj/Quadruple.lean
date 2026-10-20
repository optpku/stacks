/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.Quadruple

/-!
# Positive-degree relative projective quadruples

A relative projective quadruple bundles a positive Veronese degree with the corresponding
fixed-degree quadruple. The fixed-degree payload retains the structure morphism, invertible
module, multiplicative homogeneous maps, and the degree-one epimorphism.
-/

@[expose] public section

open CategoryTheory Opposite
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- A relative projective quadruple of positive degree over a test scheme. -/
structure RelativeProjQuadruple
    (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) (T : Scheme.{u}) where
  /-- The positive degree of the Veronese presentation. -/
  degree : ℕ
  /-- Positivity of the Veronese degree. -/
  positive : 1 ≤ degree
  /-- The structure morphism, invertible module, graded maps, and generation condition at the
  chosen degree. -/
  toDegreeQuadruple : RelativeProjDegreeQuadruple 𝒜 degree T

namespace RelativeProjQuadruple

open RingedSpace.TensorPower

variable {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf}

/-- Bundle a positive degree together with a fixed-degree relative projective quadruple. -/
def ofDegree {T : Scheme.{u}} {d : ℕ} (positive : 1 ≤ d)
    (q : RelativeProjDegreeQuadruple 𝒜 d T) : RelativeProjQuadruple 𝒜 T where
  degree := d
  positive := positive
  toDegreeQuadruple := q

/-- The structure morphism of a positive-degree relative projective quadruple. -/
def morphism {T : Scheme.{u}} (q : RelativeProjQuadruple 𝒜 T) : T ⟶ S :=
  q.toDegreeQuadruple.morphism

/-- The invertible module of a positive-degree relative projective quadruple. -/
def lineBundle {T : Scheme.{u}} (q : RelativeProjQuadruple 𝒜 T) : T.Modules :=
  q.toDegreeQuadruple.lineBundle

/-- Invertibility of the module carried by a positive-degree relative projective quadruple. -/
theorem lineBundle_invertible {T : Scheme.{u}} (q : RelativeProjQuadruple 𝒜 T) :
    Scheme.Modules.Invertible q.lineBundle :=
  q.toDegreeQuadruple.lineBundle_invertible

/-- The multiplicative family of homogeneous maps carried by a positive-degree relative
projective quadruple. -/
def psi {T : Scheme.{u}} (q : RelativeProjQuadruple 𝒜 T) (n : ℕ) :
    𝒜 (Int.ofNat (n * q.degree)) ⟶
      (Scheme.Modules.pushforward q.morphism).obj
        (RingedSpace.TensorPower.sheaf q.lineBundle n) :=
  q.toDegreeQuadruple.psi n

/-- Positivity, invertibility, the unit and multiplication laws, adjunction compatibility, and
the degree-one epimorphism of a positive-degree relative projective quadruple hold
simultaneously. -/
theorem conditions_spec {T : Scheme.{u}} (q : RelativeProjQuadruple 𝒜 T) :
    1 ≤ q.degree ∧
      Scheme.Modules.Invertible q.toDegreeQuadruple.lineBundle ∧
      (∀ U : S.Opens,
        (((q.toDegreeQuadruple.psi 0).val.app (op U)).hom
            (Eq.mp
              (RelativeProjDegreeQuadruple.sourceZeroSectionEq 𝒜 U q.degree)
              (𝒜.one (op U)))) =
          TensorPower.oneSection T.sheaf q.toDegreeQuadruple.lineBundle
            (op (q.toDegreeQuadruple.morphism ⁻¹ᵁ U))) ∧
      (∀ (U : S.Opens) (i j : ℕ)
          (x : Γ(𝒜 (Int.ofNat (i * q.degree)), U))
          (y : Γ(𝒜 (Int.ofNat (j * q.degree)), U)),
        ((q.toDegreeQuadruple.psi (i + j)).val.app (op U)).hom
            (Eq.mp
              (RelativeProjDegreeQuadruple.sourceMulSectionEq 𝒜 U i j q.degree)
              (𝒜.mul (op U) (Int.ofNat (i * q.degree))
                (Int.ofNat (j * q.degree)) x y)) =
          TensorPower.mulSection T.sheaf q.toDegreeQuadruple.lineBundle
            (op (q.toDegreeQuadruple.morphism ⁻¹ᵁ U)) i j
            (((q.toDegreeQuadruple.psi i).val.app (op U)).hom x)
            (((q.toDegreeQuadruple.psi j).val.app (op U)).hom y)) ∧
      (((Scheme.Modules.pullbackPushforwardAdjunction
          q.toDegreeQuadruple.morphism).homEquiv
          (𝒜 (Int.ofNat (1 * q.degree)))
          (RingedSpace.TensorPower.sheaf q.toDegreeQuadruple.lineBundle 1)).toFun
            q.toDegreeQuadruple.degreeOneMap = q.toDegreeQuadruple.psi 1) ∧
      Epi q.toDegreeQuadruple.degreeOneMap := by
  exact ⟨q.positive,
    RelativeProjDegreeQuadruple.conditions_spec 𝒜 q.degree q.toDegreeQuadruple⟩

end RelativeProjQuadruple

end AlgebraicGeometry
