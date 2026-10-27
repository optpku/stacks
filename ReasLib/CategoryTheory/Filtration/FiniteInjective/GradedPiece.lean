/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Finite
public import ReasLib.CategoryTheory.Filtration.FiniteInjective
public import ReasLib.CategoryTheory.Filtration.GradedPiece.Comparison
public import ReasLib.CategoryTheory.Filtration.Map.Preadditive
public import ReasLib.CategoryTheory.Preadditive.Injective.Split
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Graded Pieces after Mapping Finite Filtered-Injectives

For a finite filtered-injective object, every successor inclusion is split because its source
stage is injective.  Consequently every additive functor preserves the corresponding cokernel.
This file packages the resulting comparison between mapping a filtration before taking a graded
piece and mapping the graded piece itself.  The comparison is exposed first on objects and then
as a natural isomorphism, independently of complexes or derived functors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ZeroObject

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective.GradedPiece

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
  (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]

/-- Stage injectivity obtained directly from the input finite filtration and its injective
graded pieces. This complete proof supplies the existence certificate used by `gradedSection`.
It is kept here so that the section's data do not depend on a deferred stage-injectivity proof. -/
theorem stageInjective_proof (I : FilteredInjective.category A) (p : ℤ) :
    Injective (I.obj.obj.stage p) := by
  obtain ⟨_, b, _, hb⟩ := I.obj.property
  have step (q : ℤ) (hq : Injective (I.obj.obj.stage (q + 1))) :
      Injective (I.obj.obj.stage q) := by
    let f := I.obj.obj.succInclusion q
    letI : Mono f := by
      dsimp [f]
      infer_instance
    let S := ShortComplex.cokernelSequence f
    letI : Mono S.f := by
      change Mono f
      infer_instance
    letI : Injective S.X₁ := hq
    letI : Injective S.X₃ := I.property.injective q
    let s := ShortComplex.Splitting.ofExactOfRetraction S
      (ShortComplex.cokernelSequence_exact f)
      (Injective.factorThru (𝟙 S.X₁) S.f) (Injective.comp_factorThru (𝟙 S.X₁) S.f)
      (inferInstance : Epi S.g)
    exact Injective.of_iso s.isoBinaryBiproduct.symm inferInstance
  let upper := max b p
  have hupper : I.obj.obj.filtration.stage upper = ⊥ := by
    apply le_antisymm _ bot_le
    rw [← hb]
    exact I.obj.obj.filtration.stage_mono (le_max_left b p)
  have base : Injective (I.obj.obj.stage upper) := by
    let e : I.obj.obj.stage upper ≅ (0 : A) :=
      eqToIso (congrArg (fun P : Subobject I.obj.obj.obj ↦ (P : A)) hupper) ≪≫
        Subobject.botCoeIsoZero
    exact Injective.of_iso e.symm inferInstance
  have all (n : ℕ) : Injective (I.obj.obj.stage (upper - n)) := by
    induction n with
    | zero => simpa only [Nat.cast_zero, sub_zero] using base
    | succ n ih =>
      have heq : upper - (n + 1 : ℕ) + 1 = upper - n := by omega
      exact step (upper - (n + 1 : ℕ)) (heq.symm ▸ ih)
  have heq : upper - ((upper - p).toNat : ℤ) = p := by
    dsimp [upper]
    omega
  exact heq ▸ all (upper - p).toNat

/-- A section of the original graded-piece projection, obtained by descending `1 - r i`,
where `r` is an injective retraction of the successor inclusion `i`. -/
noncomputable def gradedSection (I : FilteredInjective.category A) (p : ℤ) :
    I.obj.obj.gradedPiece p ⟶ I.obj.obj.stage p := by
  letI : Injective (I.obj.obj.stage (p + 1)) := stageInjective_proof I (p + 1)
  let i := I.obj.obj.succInclusion p
  let r := Injective.factorThru (𝟙 _) i
  have hr : i ≫ r = 𝟙 _ := Injective.comp_factorThru (𝟙 _) i
  exact cokernel.desc i (𝟙 _ - r ≫ i) (by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hr,
      Category.id_comp, sub_self])

/-- The chosen section splits the original graded-piece projection. -/
@[reassoc (attr := simp)]
theorem gradedSection_π (I : FilteredInjective.category A) (p : ℤ) :
    gradedSection I p ≫ cokernel.π (I.obj.obj.succInclusion p) = 𝟙 _ := by
  apply (cancel_epi (cokernel.π (I.obj.obj.succInclusion p))).1
  simp only [gradedSection, ← Category.assoc, cokernel.π_desc]
  simp only [Preadditive.sub_comp, Category.id_comp, Category.comp_id, Category.assoc,
    cokernel.condition, comp_zero, sub_zero]

/-- The canonical projection from the `p`-th stage of a mapped finite filtered-injective object
to the image under `F` of its original `p`-th graded piece. -/
@[stacks 05U0 "mapped graded-piece projection on finite filtered-injectives"]
noncomputable def projection (I : FilteredInjective.category A) (p : ℤ) :
    (FilteredObject.map F I.obj.obj).stage p ⟶ F.obj (I.obj.obj.gradedPiece p) :=
  (Subobject.underlyingIso (F.map (I.obj.obj.filtration.stage p).arrow)).hom ≫
    F.map (cokernel.π (I.obj.obj.succInclusion p))

/-- The mapped successor stage is killed by the canonical projection to the image of the
original graded piece. -/
@[stacks 05U0 "mapped graded-piece projection on finite filtered-injectives"]
theorem succInclusion_projection (I : FilteredInjective.category A) (p : ℤ) :
    (FilteredObject.map F I.obj.obj).succInclusion p ≫ projection F I p = 0 := sorry

/-- The canonical comparison from the graded piece of a mapped finite filtered-injective object
to the image under `F` of the original graded piece. -/
@[stacks 05U0 "graded-piece comparison on finite filtered-injectives"]
noncomputable def comparison (I : FilteredInjective.category A) (p : ℤ) :
    (FilteredObject.map F I.obj.obj).gradedPiece p ⟶ F.obj (I.obj.obj.gradedPiece p) :=
  FilteredObject.GradedPiece.desc (FilteredObject.map F I.obj.obj) p
    (projection F I p) (succInclusion_projection F I p)

/-- The inverse comparison is the image of an original graded section, followed by the mapped
stage identification and the mapped graded-piece projection. -/
noncomputable def inverse (I : FilteredInjective.category A) (p : ℤ) :
    F.obj (I.obj.obj.gradedPiece p) ⟶ (FilteredObject.map F I.obj.obj).gradedPiece p :=
  F.map (gradedSection I p) ≫
    (Subobject.underlyingIso (F.map (I.obj.obj.filtration.stage p).arrow)).inv ≫
      cokernel.π ((FilteredObject.map F I.obj.obj).succInclusion p)

/-- Mapping a finite filtered-injective object commutes canonically with taking its `p`-th
graded piece. -/
@[stacks 05U0 "graded-piece comparison on finite filtered-injectives"]
noncomputable def iso (I : FilteredInjective.category A) (p : ℤ) :
    (FilteredObject.map F I.obj.obj).gradedPiece p ≅ F.obj (I.obj.obj.gradedPiece p) where
  hom := comparison F I p
  inv := inverse F I p
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The graded-piece comparison for a finite filtered-injective object is an isomorphism. -/
@[stacks 05U0 "graded-piece comparison on finite filtered-injectives"]
theorem comparison_isIso (I : FilteredInjective.category A) (p : ℤ) :
    IsIso (comparison F I p) := by
  change IsIso (iso F I p).hom
  infer_instance

/-- The forward map of the canonical mapped graded-piece isomorphism is the cokernel
comparison. -/
@[simp, stacks 05U0 "graded-piece comparison on finite filtered-injectives"]
theorem iso_hom (I : FilteredInjective.category A) (p : ℤ) :
    (iso F I p).hom = comparison F I p := rfl

/-- The inverse of the canonical mapped graded-piece isomorphism is the explicit inverse
comparison. -/
@[simp]
theorem iso_inv (I : FilteredInjective.category A) (p : ℤ) :
    (iso F I p).inv = inverse F I p := rfl

/-- The mapped graded-piece comparisons are natural in finite filtered-injective objects. -/
@[reassoc, stacks 05U0 "naturality of the graded-piece comparison on filtered-injectives"]
theorem comparison_naturality {I J : FilteredInjective.category A} (f : I ⟶ J) (p : ℤ) :
    (FilteredObject.Hom.map F f.hom.hom).gradedPieceMap p ≫ comparison F J p =
      comparison F I p ≫ F.map (f.hom.hom.gradedPieceMap p) := sorry

/-- The canonical mapped graded-piece isomorphisms are natural in finite
filtered-injective objects. -/
@[stacks 05U0 "naturality of the graded-piece isomorphism on filtered-injectives"]
theorem iso_naturality {I J : FilteredInjective.category A} (f : I ⟶ J) (p : ℤ) :
    (FilteredObject.Hom.map F f.hom.hom).gradedPieceMap p ≫ (iso F J p).hom =
      (iso F I p).hom ≫ F.map (f.hom.hom.gradedPieceMap p) := sorry

/-- The functor obtained by mapping a finite filtered-injective object and then taking its
`p`-th graded piece. -/
@[stacks 05U0 "mapped graded-piece functor on finite filtered-injectives"]
noncomputable abbrev mappedFunctor (p : ℤ) : FilteredInjective.category A ⥤ B :=
  FilteredInjective.inclusion A ⋙ FilteredObject.Finite.mapFunctor F ⋙
    FilteredObject.Finite.AssociatedGraded.functor B ⋙ GradedObject.eval p

/-- The `p`-th graded-piece functor on finite filtered-injective objects. -/
@[stacks 05U0 "graded-piece functor on finite filtered-injectives"]
noncomputable abbrev functor (p : ℤ) : FilteredInjective.category A ⥤ A :=
  FilteredInjective.inclusion A ⋙ FilteredObject.Finite.AssociatedGraded.functor A ⋙
    GradedObject.eval p

/-- The functor obtained by first taking a graded piece of a finite filtered-injective object
and then applying `F`. -/
@[stacks 05U0 "termwise mapped graded-piece functor on finite filtered-injectives"]
noncomputable abbrev termwiseFunctor (p : ℤ) : FilteredInjective.category A ⥤ B :=
  functor (A := A) p ⋙ F

/-- The canonical natural transformation from graded pieces after mapping to mapped graded
pieces on finite filtered-injective objects. -/
@[stacks 05U0 "natural graded-piece comparison on finite filtered-injectives"]
noncomputable def natTrans (p : ℤ) : mappedFunctor F p ⟶ termwiseFunctor F p where
  app I := comparison F I p
  naturality _ _ f := comparison_naturality F f p

/-- The canonical natural isomorphism identifying graded pieces after mapping finite
filtered-injectives with mapped graded pieces. -/
@[stacks 05U0 "natural graded-piece comparison on finite filtered-injectives"]
noncomputable def natIso (p : ℤ) : mappedFunctor F p ≅ termwiseFunctor F p :=
  NatIso.ofComponents (fun I ↦ iso F I p) (fun f ↦ iso_naturality F f p)

/-- The forward component of the natural mapped graded-piece isomorphism is the canonical
graded-piece comparison. -/
@[simp, stacks 05U0 "natural graded-piece comparison on finite filtered-injectives"]
theorem natIso_hom_app (I : FilteredInjective.category A) (p : ℤ) :
    (natIso F p).hom.app I = comparison F I p := rfl

/-- The inverse component of the natural mapped graded-piece isomorphism is the inverse of the
canonical graded-piece comparison. -/
@[simp, stacks 05U0 "natural graded-piece comparison on finite filtered-injectives"]
theorem natIso_inv_app (I : FilteredInjective.category A) (p : ℤ) :
    (natIso F p).inv.app I = (iso F I p).inv := rfl

end CategoryTheory.FilteredObject.Finite.FilteredInjective.GradedPiece
