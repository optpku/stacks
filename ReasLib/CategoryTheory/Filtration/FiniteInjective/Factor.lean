/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.FiniteInjective
public import ReasLib.CategoryTheory.Filtration.Strict
public import ReasLib.CategoryTheory.Filtration.Functors
public import Mathlib.CategoryTheory.Abelian.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.CrossRefAttribute

/-!
# Extension across Strict Monomorphisms

Maps to finite filtered-injective objects extend across strict monomorphisms. This is the
filtered analogue of `Injective.factors`, with the finite filtration retained as part of the
source mathematics.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective

variable {C : Type u} [_root_.CategoryTheory.Category.{v} C] [Abelian C]

/-! The primitive extension below uses only a supplied ambient `Injective` instance.
It tests monomorphy itself: an admitted `Mono` proof is never passed to a choice. Similarly,
the total cokernel descent tests its zero-composite condition itself. The finite recursion
stores actual extension functions, rather than reconstructing an injectivity certificate and
choosing a new function from that certificate. -/

omit [Abelian C] in
/-- The existence certificate used by `ambientExtension`. It uses only the supplied
injectivity and monomorphy assumptions, with no deferred proof. -/
theorem ambientExtension_exists {J X Y : C} [Injective J] (f : X ⟶ J) (u : X ⟶ Y)
    (hu : Mono u) : ∃ g : Y ⟶ J, u ≫ g = f :=
  @Injective.factors C _ J _ X Y f u hu

/-- A total version of ambient injective extension. For a nonmonomorphism it returns zero.
The choice in the monomorphic branch uses its own branch hypothesis and the input injectivity;
no caller-supplied proof, in particular no admitted monomorphy proof, is consumed by choice. -/
def ambientExtension {J X Y : C} [Injective J] (f : X ⟶ J) (u : X ⟶ Y) : Y ⟶ J := by
  classical
  exact if hu : Mono u then (ambientExtension_exists f u hu).choose else 0

/-- On monomorphisms the total ambient extension restricts to the original map. -/
theorem ambientExtension_fac {J X Y : C} [Injective J] (f : X ⟶ J) (u : X ⟶ Y)
    [Mono u] : u ≫ ambientExtension f u = f := by
  classical
  rw [ambientExtension, dif_pos (inferInstance : Mono u)]
  exact (ambientExtension_exists f u inferInstance).choose_spec

/-- Cokernel descent as a total map on ambient morphisms. The incompatible case is zero.
Its data do not take a proof of the zero-composite condition as an argument. -/
def cokernelDescOrZero {X Y Z : C} (u : X ⟶ Y) (f : Y ⟶ Z) : cokernel u ⟶ Z := by
  classical
  exact if h : u ≫ f = 0 then cokernel.desc u f h else 0

/-- The total descent agrees with the specified cokernel descent on compatible inputs. -/
theorem cokernelDescOrZero_eq {X Y Z : C} (u : X ⟶ Y) (f : Y ⟶ Z)
    (h : u ≫ f = 0) : cokernelDescOrZero u f = cokernel.desc u f h := by
  classical
  rw [cokernelDescOrZero, dif_pos h]

/-- A total quotient map built from the underlying ambient map. This avoids choosing stage
maps from the filtration-preservation laws of recursively constructed filtered morphisms. -/
def quotientMapHom (A B : FilteredObject C) (u : A.obj ⟶ B.obj) (p : ℤ) :
    A.quotient p ⟶ B.quotient p :=
  cokernelDescOrZero (A.filtration.stage p).arrow
    (u ≫ cokernel.π (B.filtration.stage p).arrow)

/-- Preservation of the original filtration by a map into a filtration stage. -/
def StagePreserving (I A : FilteredObject C) (p : ℤ) (f : A.obj ⟶ I.stage p) : Prop :=
  ∀ q : ℤ, (I.filtration.stage q).Factors
    ((A.filtration.stage q).arrow ≫ f ≫ (I.filtration.stage p).arrow)

/-- Data of one stage of the finite recursion. Both ambient and filtered extension functions
are stored directly. Their laws are proved separately, and no injectivity/existence certificate
is stored or used as a source of data at the next step. -/
structure StageExtension (I : FilteredObject C) (p : ℤ) where
  /-- Total ambient extension into this stage. -/
  ambient {X Y : C} (f : X ⟶ I.stage p) (u : X ⟶ Y) : Y ⟶ I.stage p
  /-- Total filtered extension into this stage, before bundling preservation. -/
  filtered (A B : FilteredObject C) (f : A.obj ⟶ I.stage p) (u : A.obj ⟶ B.obj) :
    B.obj ⟶ I.stage p

namespace StageExtension

/-- The recursion starts at the zero stage with two literal zero functions. No existence
certificate, including a zero-object injectivity certificate, is selected from. -/
def zero (I : FilteredObject C) (p : ℤ) : StageExtension I p where
  ambient := fun _ _ ↦ 0
  filtered := fun _ _ _ _ ↦ 0

/-- The retraction is an evaluation of the already stored ambient extension function. -/
def retraction {I : FilteredObject C} (p : ℤ) (S : StageExtension I (p + 1)) :
    I.stage p ⟶ I.stage (p + 1) :=
  S.ambient (𝟙 _) (I.succInclusion p)

/-- The complementary graded section is the total cokernel descent of `1 - r i`.
Its formula uses no inverse or splitting-existence certificate. -/
def section_ {I : FilteredObject C} (p : ℤ) (S : StageExtension I (p + 1)) :
    I.gradedPiece p ⟶ I.stage p :=
  cokernelDescOrZero (I.succInclusion p) (𝟙 _ - retraction p S ≫ I.succInclusion p)

/-- The graded part is extended on the quotient by the next source stage. The only
injectivity consumed here is the input object's original graded-piece injectivity. -/
def gradedExtension {I : FilteredObject C} [FilteredObject.IsFilteredInjective I]
    (A B : FilteredObject C) (p : ℤ) (f : A.obj ⟶ I.stage p) (u : A.obj ⟶ B.obj) :
    B.obj ⟶ I.gradedPiece p :=
  cokernel.π (B.filtration.stage (p + 1)).arrow ≫
    ambientExtension
      (cokernelDescOrZero (A.filtration.stage (p + 1)).arrow
        (f ≫ cokernel.π (I.succInclusion p)))
      (quotientMapHom A B u (p + 1))

/-- Descend one stage by the explicit two-component formula, for both stored extension
functions. The retraction is evaluated from `S.ambient`; only a graded piece uses choice. -/
def descend {I : FilteredObject C} [FilteredObject.IsFilteredInjective I]
    (p : ℤ) (S : StageExtension I (p + 1)) : StageExtension I p where
  ambient := fun f u ↦
    S.ambient (f ≫ retraction p S) u ≫ I.succInclusion p +
      ambientExtension (f ≫ cokernel.π (I.succInclusion p)) u ≫ section_ p S
  filtered := fun A B f u ↦
    S.filtered A B (f ≫ retraction p S) u ≫ I.succInclusion p +
      gradedExtension A B p f u ≫ section_ p S

/-- The actual finite descending recursion. The initial zero-stage bound is used only in
its correctness laws, rather than as a certificate from which to select data. -/
def iterate (I : FilteredObject C) [FilteredObject.IsFilteredInjective I]
    (b : ℤ) : (n : ℕ) → StageExtension I (b - n)
  | 0 => by simpa using zero I b
  | n + 1 => by
      have S : StageExtension I ((b - (n + 1 : ℕ)) + 1) := by
        have heq : b - (n : ℤ) = b - (n + 1 : ℕ) + 1 := by omega
        exact heq ▸ iterate I b n
      exact descend (b - (n + 1 : ℕ)) S

end StageExtension

/-- The underlying extension map for fixed filtration bounds. This is total in the input
maps and contains no filtration-preservation, strictness or monomorphy proof argument. -/
def extendAtBoundsHom {I : FilteredObject.Finite.category C}
    [FilteredObject.IsFilteredInjective I.obj] (A B : FilteredObject C)
    (a b : ℤ) (hab : a ≤ b) (ha : I.obj.filtration.stage a = ⊤)
    (f : A.obj ⟶ I.obj.obj) (u : A.obj ⟶ B.obj) : B.obj ⟶ I.obj.obj := by
  let S : StageExtension I.obj a := by
    have heq : b - ((b - a).toNat : ℤ) = a := by omega
    exact heq ▸ StageExtension.iterate I.obj b (b - a).toNat
  let e : I.obj.stage a ≅ I.obj.obj :=
    eqToIso (congrArg (fun P : Subobject I.obj.obj ↦ (P : C)) ha) ≪≫
      Subobject.underlyingIso (𝟙 I.obj.obj)
  exact S.filtered A B (f ≫ e.inv) u ≫ (I.obj.filtration.stage a).arrow

/-- The underlying objectwise extension chooses only the input finite-filtration bounds.
All subsequent maps are evaluations of the explicit finite recursion. -/
def extendHom {I : FilteredObject.Finite.category C} [FilteredObject.IsFilteredInjective I.obj]
    (A B : FilteredObject C) (f : A.obj ⟶ I.obj.obj) (u : A.obj ⟶ B.obj) :
    B.obj ⟶ I.obj.obj := by
  let a : ℤ := Classical.choose I.property
  let b : ℤ := Classical.choose (Classical.choose_spec I.property)
  have ha : I.obj.filtration.stage a = ⊤ :=
    (Classical.choose_spec (Classical.choose_spec I.property)).1
  have hmin : I.obj.filtration.stage (min a b) = ⊤ := by
    apply le_antisymm le_top
    rw [← ha]
    exact I.obj.filtration.stage_mono (min_le_left a b)
  exact extendAtBoundsHom A B (min a b) b (min_le_right _ _) hmin f u

/-- The total underlying formula preserves the filtration on the source-faithful inputs. -/
theorem extendHom_preserves {A B : FilteredObject C} {I : FilteredObject.Finite.category C}
    [FilteredObject.IsFilteredInjective I.obj] (f : A ⟶ I.obj) (u : A ⟶ B)
    [Mono u.hom] (hu : FilteredObject.Hom.Strict u) (p : ℤ) :
    (I.obj.filtration.stage p).Factors
      ((B.filtration.stage p).arrow ≫ extendHom A B f.hom u.hom) := sorry

/-- The specified objectwise extension. Its underlying map is the explicit total recursion;
filtration preservation is a separate proof law and cannot influence any extension choice. -/
@[stacks 05TR "explicit extension across a strict monomorphism"]
def extend {A B : FilteredObject C} {I : FilteredObject.Finite.category C}
    [FilteredObject.IsFilteredInjective I.obj] (f : A ⟶ I.obj) (u : A ⟶ B)
    [Mono u.hom] (hu : FilteredObject.Hom.Strict u) : B ⟶ I.obj :=
  FilteredObject.Hom.mk (extendHom A B f.hom u.hom) (extendHom_preserves f u hu)

/-- Computation of the actual ambient extension map. -/
@[simp]
theorem extend_hom {A B : FilteredObject C} {I : FilteredObject.Finite.category C}
    [FilteredObject.IsFilteredInjective I.obj] (f : A ⟶ I.obj) (u : A ⟶ B)
    [Mono u.hom] (hu : FilteredObject.Hom.Strict u) :
    (extend f u hu).hom = extendHom A B f.hom u.hom := rfl

/-- The explicit extension restricts to the given map. -/
@[reassoc, stacks 05TR "restriction of the explicit filtered-injective extension"]
theorem extend_fac {A B : FilteredObject C} {I : FilteredObject.Finite.category C}
    [FilteredObject.IsFilteredInjective I.obj] (f : A ⟶ I.obj) (u : A ⟶ B)
    [Mono u.hom] (hu : FilteredObject.Hom.Strict u) : u ≫ extend f u hu = f := sorry

/-- Lemma 13.26.4 (`05TR`): a map to a finite filtered-injective object extends across a strict
monomorphism.  The witness is the explicit finite recursion `extend`. -/
@[stacks 05TR]
theorem factors {A B : FilteredObject C} {I : FilteredObject.Finite.category C}
    [FilteredObject.IsFilteredInjective I.obj] (f : A ⟶ I.obj) (u : A ⟶ B)
    [Mono u.hom] (hu : FilteredObject.Hom.Strict u) :
    ∃ g : B ⟶ I.obj, u ≫ g = f :=
  ⟨extend f u hu, extend_fac f u hu⟩

end CategoryTheory.FilteredObject.Finite.FilteredInjective
