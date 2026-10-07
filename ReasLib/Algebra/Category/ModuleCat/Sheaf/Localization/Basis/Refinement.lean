module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Basis.Presentation
public import ReasLib.CategoryTheory.Limits.Cokernel.Refinement
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite refinements of presentations by localized structure modules

For a finite family of basis objects, a chosen finite subfamily of each covering family gives a
canonical map between the corresponding coproducts of localized structure modules.  The main
result supplies a finite basis refinement of any map between finite coproducts and packages the
resulting cokernel comparison using `CategoryTheory.Limits.CokernelRefinement`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe z w v u

namespace SheafOfModules.Localization.Basis

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (R : Sheaf J RingCat.{w}) (B : Set C)
variable [∀ U : C, (restriction R U : SheafOfModules.{w} R ⥤
  SheafOfModules.{w} (R.over U)).IsRightAdjoint]

namespace SelectedCover

/-- The index type of finite subfamilies selected from a finite family of covering families. -/
abbrev Index {n : ℕ} {K : Fin n → Type z} (K' : ∀ i, Finset (K i)) :=
  Σ i, K' i

/-- The site object indexed by a member of the selected finite covering families. -/
abbrev obj {n : ℕ} {K : Fin n → Type z}
    (Ucover : ∀ i, K i → C) (K' : ∀ i, Finset (K i)) (a : Index K') : C :=
  Ucover a.1 a.2

/-- The canonical coproduct map induced by finite subfamilies of covers of the objects `U i`. -/
@[stacks 093F "selected-cover map"]
noncomputable def map {n : ℕ} {K : Fin n → Type z}
    (U : Fin n → C) (Ucover : ∀ i, K i → C)
    (π : ∀ i k, Ucover i k ⟶ U i) (K' : ∀ i, Finset (K i)) :
    (∐ fun a : Index K' ↦ structureModule R (obj Ucover K' a)) ⟶
      (∐ fun i ↦ structureModule R (U i)) :=
  Sigma.desc fun a ↦
    structureModuleMap R (π a.1 a.2) ≫
      Sigma.ι (fun i ↦ structureModule R (U i)) a.1

end SelectedCover

/-- Lemma 18.30.9 (093F), sieve-saturated specialization: a map between finite coproducts of
basis structure modules admits a finite refinement inducing an isomorphism on cokernels. -/
@[stacks 093F "sieve-saturated specialization"]
theorem exists_finiteCokernelRefinement
    (h_enough : J.HasEnoughObjectsWithProperty (fun U ↦ U ∈ B))
    (h_compact : GrothendieckTopology.Basis.IsQuasiCompact J B)
    (h_overlaps : GrothendieckTopology.Basis.HasQuasiCompactOverlaps J B)
    {n m : ℕ} (U : Fin n → C) (V : Fin m → C)
    (hU : ∀ i, U i ∈ B) (hV : ∀ j, V j ∈ B)
    {K : Fin n → Type z} (Ucover : ∀ i, K i → C)
    (π : ∀ i k, Ucover i k ⟶ U i)
    (hUcover : ∀ i k, Ucover i k ∈ B)
    (hcover : ∀ i, Sieve.ofArrows (Ucover i) (π i) ∈ J (U i))
    (f : (∐ fun j ↦ structureModule R (V j)) ⟶
      (∐ fun i ↦ structureModule R (U i))) :
    ∃ (K' : ∀ i, Finset (K i)) (l : ℕ) (W : Fin l → C),
      (∀ a, W a ∈ B) ∧
        ∃ top : (∐ fun a ↦ structureModule R (W a)) ⟶
            (∐ fun a : SelectedCover.Index K' ↦
              structureModule R (SelectedCover.obj Ucover K' a)),
          ∃ sq : CokernelRefinement top f,
            sq.right = SelectedCover.map R U Ucover π K' := sorry

end SheafOfModules.Localization.Basis

namespace SheafOfModules.Localization.Basis

variable {C : Type u} [Category.{v} C] {K : Coverage C}
variable [HasWeakSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [K.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (R : Sheaf K.toGrothendieck RingCat.{w}) (B : Set C)
variable [∀ U : C, (restriction R U : SheafOfModules.{w} R ⥤
  SheafOfModules.{w} (R.over U)).IsRightAdjoint]

/-- Lemma 18.30.9 (093F): under the three chosen-cover quasi-compact-basis hypotheses, a map
between finite coproducts of basis structure modules admits a finite refinement by selected
members of the given basis covers, inducing an isomorphism on cokernels. -/
@[stacks 093F]
theorem existsFiniteCokernelRefinement
    (hEnough : K.HasEnoughObjectsWithProperty (fun U ↦ U ∈ B))
    (hCompact : CategoryTheory.Coverage.Basis.IsQuasiCompact K B)
    (hOverlaps : CategoryTheory.Coverage.Basis.HasQuasiCompactOverlaps K B)
    {n m : ℕ} (U : Fin n → C) (V : Fin m → C)
    (hU : ∀ i, U i ∈ B) (hV : ∀ j, V j ∈ B)
    {I : Fin n → Type z} (Ucover : ∀ i, I i → C)
    (π : ∀ i k, Ucover i k ⟶ U i)
    (hUcover : ∀ i k, Ucover i k ∈ B)
    (hCover : ∀ i, Presieve.ofArrows (Ucover i) (π i) ∈ K (U i))
    (f : (∐ fun j ↦ structureModule R (V j)) ⟶
      (∐ fun i ↦ structureModule R (U i))) :
    ∃ (I' : ∀ i, Finset (I i)) (l : ℕ) (W : Fin l → C),
      (∀ a, W a ∈ B) ∧
        ∃ top : (∐ fun a ↦ structureModule R (W a)) ⟶
            (∐ fun a : SelectedCover.Index I' ↦
              structureModule R (SelectedCover.obj Ucover I' a)),
          ∃ sq : CokernelRefinement top f,
            sq.right = SelectedCover.map R U Ucover π I' := sorry

end SheafOfModules.Localization.Basis
