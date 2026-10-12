/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.FormalObjectSystem
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap97.«97_5_0_1_Restrict»
public import stacks_project.Chap98.Definition_98_11_1_LimitPreserving
public import stacks_project.Chap98.Definition_98_13_1_Openness
public import stacks_project.Chap98.Definition_98_18_1
public import stacks_project.Chap98.Lemma_98_20_3
import Mathlib.Tactic.CrossRefAttribute

/-!
# Openness of versality of the diagonal from a strong formal effectiveness axiom

On a locally Noetherian base, a category fibred in groupoids over `(Sch/S)_fppf`
with representable-by-algebraic-spaces double diagonal, (RS*), and limit
preservation, and for which Remark 98.20.2 systems with pairwise square-zero
kernels have fully faithful limit-fibre comparison, has openness of versality
of its diagonal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor.Fiber
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u v w

namespace AlgebraicGeometry.FormalObjectSystem

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C] {p : C ⥤ Over S}
variable (ξ : FormalObjectSystem p)

/-- The comparison morphism `Spec(R_n) ⟶ Spec(lim R_n)` in `Over S`. -/
def stageToLimitOver (n : ℕ) : ξ.stageOver n ⟶ ξ.limitOver :=
  Over.homMk (ξ.stageToLimitScheme n) (ξ.stageToLimit_comp n)

/-- The underlying scheme morphism of `stageToLimitOver n` is `stageToLimitScheme n`. -/
theorem stageToLimitOver_left (n : ℕ) :
    (ξ.stageToLimitOver n).left = ξ.stageToLimitScheme n :=
  sorry

/-- The successor morphism `Spec(R_n) ⟶ Spec(R_{n+1})` in `Over S`. -/
def stageStep (n : ℕ) : ξ.stageOver n ⟶ ξ.stageOver (n + 1) :=
  Over.homMk (Spec.map (ξ.ringSystem.stepMap n)) (ξ.step_comp n)

/-- The underlying scheme morphism of `stageStep n` is `Spec.map` of the successor
ring transition. -/
theorem stageStep_left (n : ℕ) :
    (ξ.stageStep n).left = Spec.map (ξ.ringSystem.stepMap n) :=
  sorry

/-- Stage comparison factors through the successor: `stageToLimitOver n` equals
`stageStep n ≫ stageToLimitOver (n + 1)`. -/
theorem stageToLimitOver_succ (n : ℕ) :
    ξ.stageToLimitOver n = ξ.stageStep n ≫ ξ.stageToLimitOver (n + 1) :=
  sorry

variable [p.IsFibered]

/-- A compatible family of fibre morphisms over the stages `Spec(R_n)`, the Hom-data
of an object of `lim_n X_{Spec(R_n)}`. -/
structure CompatibleStageHom (x y : p.Fiber ξ.limitOver) where
  /-- The fibre morphism over `Spec(R_n)`. -/
  app : ∀ n, restrictObj x (ξ.stageToLimitOver n) ⟶ restrictObj y (ξ.stageToLimitOver n)
  /-- Successive components are compatible under restriction along `stageStep n`. -/
  naturality : ∀ n,
    restrictHom (app (n + 1)) (ξ.stageStep n) =
      (restrictObj_comp x (ξ.stageToLimitOver (n + 1)) (ξ.stageStep n) ≪≫
          restrictObj_eq x (ξ.stageToLimitOver_succ n).symm).hom ≫
        app n ≫
          (restrictObj_comp y (ξ.stageToLimitOver (n + 1)) (ξ.stageStep n) ≪≫
              restrictObj_eq y (ξ.stageToLimitOver_succ n).symm).inv

/-- Restriction of a fibre morphism over `Spec(lim R_n)` along every
`stageToLimitOver n`. -/
def compatibleStageHom {x y : p.Fiber ξ.limitOver} (φ : x ⟶ y) :
    CompatibleStageHom ξ x y where
  app n := restrictHom φ (ξ.stageToLimitOver n)
  naturality := sorry

/-- The `n`th component of `compatibleStageHom φ` is restriction along
`stageToLimitOver n`. -/
theorem compatibleStageHom_app {x y : p.Fiber ξ.limitOver} (φ : x ⟶ y) (n : ℕ) :
    (ξ.compatibleStageHom φ).app n = restrictHom φ (ξ.stageToLimitOver n) :=
  sorry

/-- The comparison `X_{Spec(lim R_n)} ⟶ lim_n X_{Spec(R_n)}` is fully faithful:
fibre morphisms over the limiting spectrum correspond bijectively to compatible
stage morphisms. -/
def IsLimitComparisonFullyFaithful : Prop :=
  ∀ (x y : p.Fiber ξ.limitOver),
    Function.Bijective (fun φ : x ⟶ y ↦ ξ.compatibleStageHom φ)

/-- Fully faithfulness of the limit-fibre comparison is injectivity of restriction
from the limit together with surjectivity onto compatible stage Hom-families. -/
theorem isLimitComparisonFullyFaithful_iff :
    ξ.IsLimitComparisonFullyFaithful ↔
      ∀ (x y : p.Fiber ξ.limitOver),
        Function.Injective (fun φ : x ⟶ y ↦ ξ.compatibleStageHom φ) ∧
          ∀ fam : CompatibleStageHom ξ x y,
            ∃! φ : x ⟶ y, ξ.compatibleStageHom φ = fam :=
  sorry

end AlgebraicGeometry.FormalObjectSystem

namespace AlgebraicGeometry.Groupoids.Hom

open AlgebraicGeometry.GroupoidsOver

/-- Remark 98.20.4: let `S` be a locally Noetherian scheme and let `X` be a
category fibred in groupoids over `(Sch/S)_fppf`. Assume the double diagonal
`Hom.diagonal (diagonal X) : X ⟶ X ×_{X × X} X` is representable by algebraic
spaces, `X` has (RS*), `X` is limit preserving, and for inverse systems of
`S`-algebras as in Remark 98.20.2 with `Ker(R_m ⟶ R_n)` square zero for all
`m ≥ n` the functor `X_{Spec(lim R_n)} ⟶ lim_n X_{Spec(R_n)}` is fully
faithful. Then the diagonal `Δ : X ⟶ X × X` satisfies openness of versality.
This follows by applying Lemma 98.20.3 to the slices
`fiberProductSlice (diagonal X) hV y hy` for affine `V` locally of finite
presentation over `S` and objects `y` of `X × X` over `V`. -/
@[stacks 0CXV]
theorem OpennessOfVersality.diagonal_of_squareZeroKernelFullyFaithful
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] [Groupoids.LimitPreserving X]
    (h_ddiag :
      relativelyRepresentableByAlgebraicSpaces
        (Hom.diagonal.{u + 1, u, u + 1}
          (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X)))
    (h_ff :
      ∀ ξ : FormalObjectSystem X.p,
        ξ.KernelSquareZero → ξ.IsLimitComparisonFullyFaithful) :
    OpennessOfVersality
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
