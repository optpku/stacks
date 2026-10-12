/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import stacks_project.Chap56.«56_5_1_1_FourierMukai»
public import stacks_project.Chap56.Lemma_56_5_5
public import stacks_project.Chap56.Lemma_56_5_7_ExactAdmissible

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R]
variable {X Y Z : Scheme.{u}}

variable (x : X ⟶ Spec (CommRingCat.of R))
variable (y : Y ⟶ Spec (CommRingCat.of R))
variable (z : Z ⟶ Spec (CommRingCat.of R))

/-- The triple fiber product `X ×_R Y ×_R Z`, realized as the pullback of
`Y ×_R Z → Spec R` along `X ×_R Y → Spec R` via `Limits.pullback.snd x y ≫ y`. -/
abbrev tripleFiber : Scheme.{u} :=
  Limits.pullback (Limits.pullback.snd x y ≫ y) z

/-- The projection `pr₁₂ : X ×_R Y ×_R Z ⟶ X ×_R Y`. -/
noncomputable def pr12 : tripleFiber x y z ⟶ Limits.pullback x y :=
  Limits.pullback.fst (Limits.pullback.snd x y ≫ y) z

/-- The two legs of `pr₂₃` commute over `Spec R`. -/
theorem pr23_condition :
    (Limits.pullback.fst (Limits.pullback.snd x y ≫ y) z ≫ Limits.pullback.snd x y) ≫
        y =
      Limits.pullback.snd (Limits.pullback.snd x y ≫ y) z ≫ z :=
  sorry

/-- The projection `pr₂₃ : X ×_R Y ×_R Z ⟶ Y ×_R Z`. -/
noncomputable def pr23 : tripleFiber x y z ⟶ Limits.pullback y z :=
  Limits.pullback.lift
    (Limits.pullback.fst (Limits.pullback.snd x y ≫ y) z ≫ Limits.pullback.snd x y)
    (Limits.pullback.snd (Limits.pullback.snd x y ≫ y) z)
    (pr23_condition x y z)

/-- The two legs of `pr₁₃` commute over `Spec R`. -/
theorem pr13_condition :
    (Limits.pullback.fst (Limits.pullback.snd x y ≫ y) z ≫ Limits.pullback.fst x y) ≫
        x =
      Limits.pullback.snd (Limits.pullback.snd x y ≫ y) z ≫ z :=
  sorry

/-- The projection `pr₁₃ : X ×_R Y ×_R Z ⟶ X ×_R Z`. -/
noncomputable def pr13 : tripleFiber x y z ⟶ Limits.pullback x z :=
  Limits.pullback.lift
    (Limits.pullback.fst (Limits.pullback.snd x y ≫ y) z ≫ Limits.pullback.fst x y)
    (Limits.pullback.snd (Limits.pullback.snd x y ≫ y) z)
    (pr13_condition x y z)

/-- Compatibility of `pr₁₂` with the projection to `Y`. -/
theorem pr12_comp_snd :
    pr12 x y z ≫ Limits.pullback.snd x y =
      Limits.pullback.fst (Limits.pullback.snd x y ≫ y) z ≫
        Limits.pullback.snd x y := sorry

/-- Compatibility of `pr₂₃` with the projection to `Y`. -/
theorem pr23_comp_fst :
    pr23 x y z ≫ Limits.pullback.fst y z =
      Limits.pullback.fst (Limits.pullback.snd x y ≫ y) z ≫
        Limits.pullback.snd x y := sorry

/-- Compatibility of `pr₁₃` with the projection to `X`. -/
theorem pr13_comp_fst :
    pr13 x y z ≫ Limits.pullback.fst x z =
      Limits.pullback.fst (Limits.pullback.snd x y ≫ y) z ≫
        Limits.pullback.fst x y := sorry

/-- Quasi-compactness of `pr₁₃` under the standing quasi-compact affine-diagonal
hypotheses on `X` and `Y`. -/
instance quasiCompact_pr13
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    [IsAffineHom (prod.lift (𝟙 Y) (𝟙 Y))] :
    QuasiCompact (pr13 x y z) := sorry

/-- Quasi-separatedness of `pr₁₃` under the standing quasi-compact affine-diagonal
hypotheses on `X` and `Y`. -/
instance quasiSeparated_pr13
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    [IsAffineHom (prod.lift (𝟙 Y) (𝟙 Y))] :
    QuasiSeparated (pr13 x y z) := sorry

/-- The convolution kernel
`pr₁₃,*(pr₁₂^* K ⊗ pr₂₃^* L)` on `X ×_R Z`. -/
noncomputable def composeKernel
    [QuasiCompact (pr13 x y z)] [QuasiSeparated (pr13 x y z)]
    (K : Scheme.QCoh (Limits.pullback x y))
    (L : Scheme.QCoh (Limits.pullback y z)) :
    Scheme.QCoh (Limits.pullback x z) :=
  (Scheme.QCoh.pushforward (pr13 x y z)).obj
    ((tensorRight ((Scheme.QCoh.pullback (pr23 x y z)).obj L)).obj
      ((Scheme.QCoh.pullback (pr12 x y z)).obj K))

/-- Unfolding of `composeKernel` as
`pr₁₃,*(pr₁₂^* K ⊗ pr₂₃^* L)`. -/
theorem composeKernel_obj
    [QuasiCompact (pr13 x y z)] [QuasiSeparated (pr13 x y z)]
    (K : Scheme.QCoh (Limits.pullback x y))
    (L : Scheme.QCoh (Limits.pullback y z)) :
    composeKernel x y z K L =
      (Scheme.QCoh.pushforward (pr13 x y z)).obj
        ((tensorRight ((Scheme.QCoh.pullback (pr23 x y z)).obj L)).obj
          ((Scheme.QCoh.pullback (pr12 x y z)).obj K)) := sorry


end AlgebraicGeometry.Scheme.QCoh
