/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap56.Lemma_56_5_4_Pullback
public import stacks_project.Chap56.Lemma_56_5_7_Kernel

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R] {X Y T : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))
variable (t : T ⟶ Spec (CommRingCat.of R))

/-- The iterated fiber product `T ×_R X ×_R Y`, modeled as
`(T ×_R X) ×_R Y`. -/
noncomputable def triplePullback : Scheme.{u} :=
  Limits.pullback (Limits.pullback.snd t x ≫ x) y

/-- The projection `pr₁₂ : T ×_R X ×_R Y ⟶ T ×_R X`. -/
noncomputable def pr12 : triplePullback x y t ⟶ Limits.pullback t x :=
  Limits.pullback.fst (Limits.pullback.snd t x ≫ x) y

/-- The projection `pr₂₃ : T ×_R X ×_R Y ⟶ X ×_R Y`. -/
noncomputable def pr23 : triplePullback x y t ⟶ Limits.pullback x y :=
  pullbackMapFst x y (Limits.pullback.snd t x)

/-- The projection `pr₁₃ : T ×_R X ×_R Y ⟶ T ×_R Y`. -/
noncomputable def pr13 : triplePullback x y t ⟶ Limits.pullback t y :=
  Limits.pullback.map (Limits.pullback.snd t x ≫ x) y t y
    (Limits.pullback.fst t x) (𝟙 Y) (𝟙 _)
    ((Category.comp_id (Limits.pullback.snd t x ≫ x)).trans
      (Limits.pullback.condition (f := t) (g := x)).symm)
    ((Category.id_comp y).trans (Category.comp_id y).symm)



/-- The sheaf `pr₁₂^* F ⊗ pr₂₃^* K` on `T ×_R X ×_R Y`. -/
noncomputable def tensorPullback_triple (K : Scheme.QCoh (Limits.pullback x y))
    (F : Scheme.QCoh (Limits.pullback t x)) :
    (triplePullback x y t).Modules :=
  ((tensorRight ((Scheme.QCoh.pullback (pr23 x y t)).obj K)).obj
    ((Scheme.QCoh.pullback (pr12 x y t)).obj F)).obj

/-- `pr₁₂` is the first projection of `(T ×_R X) ×_R Y`. -/
theorem pr12_eq_fst :
    pr12 x y t = Limits.pullback.fst (Limits.pullback.snd t x ≫ x) y := sorry

variable [HasInjectiveResolutions (triplePullback x y t).Modules]

/-- The higher direct image `R^q pr₁₃,*(pr₁₂^* F ⊗ pr₂₃^* K)`. -/
noncomputable def higherDirectImage_tripleTensor
    (K : Scheme.QCoh (Limits.pullback x y))
    (F : Scheme.QCoh (Limits.pullback t x)) (q : ℕ) :
    (Limits.pullback t y).Modules :=
  ((Scheme.Modules.pushforward (pr13 x y t)).rightDerived q).obj
    (tensorPullback_triple x y t K F)

end AlgebraicGeometry.Scheme.QCoh
