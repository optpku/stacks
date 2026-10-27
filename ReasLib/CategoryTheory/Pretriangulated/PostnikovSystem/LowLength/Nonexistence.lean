/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.LowLength
public import Mathlib.Data.Fin.Basic

/-!
# Lengthwise existence and extension for finite Postnikov systems

This leaf packages the two uniform properties whose failure first occurs in lengths two and
three: extension of row morphisms to chosen Postnikov systems, and existence of a Postnikov
system on every complex row. Keeping the ambient-category quantification outside these predicates
makes obstruction statements usable without repeating the full finite-system signature.
-/

@[expose] public section

open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory

variable (D : Type u) [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

namespace PostnikovSystem

/-- Every complex row of length `n` in `D` admits a finite Postnikov system. -/
@[stacks 0D81 "lengthwise existence of finite Postnikov systems"]
def ExistsAtLength (n : ℕ) : Prop :=
  ∀ (X : ComposableArrows D n), X.IsComplex → Nonempty (PostnikovSystem X)

namespace ExistsAtLength

/-- Apply lengthwise existence to a complex row. -/
theorem nonempty {n : ℕ} (h : ExistsAtLength D n) (X : ComposableArrows D n)
    (hX : X.IsComplex) :
    Nonempty (PostnikovSystem X) := by
  exact h X hX

/-- Every triangulated category has finite Postnikov systems in length zero. -/
@[stacks 0D81 "uniform length-zero Postnikov-system existence"]
theorem zero : ExistsAtLength D 0 := by
  intro X _
  exact ⟨PostnikovSystem.mk₀ (X.obj 0) (𝟙 _)⟩

/-- Every triangulated category has finite Postnikov systems in length one. -/
@[stacks 0D81 "uniform length-one Postnikov-system existence"]
theorem one : ExistsAtLength D 1 := by
  intro X _
  obtain ⟨Y, f, connecting, hT⟩ := distinguished_cocone_triangle₁ (X.map' 0 1)
  exact ⟨mkSucc (PostnikovSystem.mk₀ (X.δ₀.obj 0) (𝟙 _)) Y f (X.map' 0 1)
    connecting hT (Category.comp_id _)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every triangulated category has finite Postnikov systems on complex rows in length two. -/
@[stacks 0D81 "uniform length-two Postnikov-system existence"]
theorem two : ExistsAtLength D 2 := by
  intro X hX
  obtain ⟨Y, f, connecting, hT⟩ := distinguished_cocone_triangle₁ (X.map' 1 2)
  let P₀ : PostnikovSystem X.δ₀.δ₀ := PostnikovSystem.mk₀ (X.δ₀.δ₀.obj 0) (𝟙 _)
  let P₁ : PostnikovSystem X.δ₀ :=
    mkSucc P₀ Y f (X.map' 1 2) connecting hT (Category.comp_id _)
  obtain ⟨g, hg⟩ := Pretriangulated.Triangle.coyoneda_exact₂
    (Triangle.mk f (X.map' 1 2) connecting) hT (X.map' 0 1) (hX.zero 0)
  obtain ⟨Z, toX, δ, hZ⟩ := distinguished_cocone_triangle₁ g
  exact ⟨mkSucc P₁ Z toX g δ hZ hg.symm⟩

end ExistsAtLength

namespace Morphism

/-- Every row morphism of length `n` extends between any chosen Postnikov systems. -/
@[stacks 0D81 "lengthwise extension of finite Postnikov-system morphisms"]
def ExtendsAtLength (n : ℕ) : Prop :=
  ∀ {X X' : ComposableArrows D n} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X'), Nonempty (PostnikovSystem.Morphism P P' φ)

namespace ExtendsAtLength

/-- Apply lengthwise morphism extension to chosen finite Postnikov systems. -/
theorem nonempty {n : ℕ} (h : ExtendsAtLength D n)
    {X X' : ComposableArrows D n} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X') :
    Nonempty (PostnikovSystem.Morphism P P' φ) := by
  exact h P P' φ

/-- Row morphisms between length-zero finite Postnikov systems always extend. -/
@[stacks 0D81 "uniform length-zero Postnikov morphism extension"]
theorem zero : ExtendsAtLength D 0 := by
  intro X X' P P' φ
  haveI : IsIso P'.headToX := by
    rcases P' with ⟨Y, toX, step⟩
    cases step
    infer_instance
  refine ⟨{
    yMap := fun i => by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact P.headToX ≫ φ.app 0 ≫ inv P'.headToX
    comm_toX := ?_
    comm_toNext := fun i => Fin.elim0 i
    comm_connecting := fun i => Fin.elim0 i }⟩
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  constructor
  change P.headToX ≫ φ.app 0 =
    (P.headToX ≫ φ.app 0 ≫ inv P'.headToX) ≫ P'.headToX
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Row morphisms between length-one finite Postnikov systems always extend. -/
@[stacks 0D81 "uniform length-one Postnikov morphism extension"]
theorem one : ExtendsAtLength D 1 := by
  intro X X' P P' φ
  haveI : IsIso P'.tail.headToX := by
    rcases P'.tail with ⟨Y, toX, step⟩
    cases step
    infer_instance
  let e : P.tail.head ⟶ P'.tail.head :=
    P.tail.headToX ≫ φ.app 1 ≫ inv P'.tail.headToX
  have he : e ≫ P'.tail.headToX = P.tail.headToX ≫ φ.app 1 := by
    dsimp only [e]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have comm : P.headToNext ≫ e = φ.app 0 ≫ P'.headToNext := by
    apply (cancel_mono P'.tail.headToX).1
    calc
      (P.headToNext ≫ e) ≫ P'.tail.headToX =
          P.headToNext ≫ (P.tail.headToX ≫ φ.app 1) := by rw [Category.assoc, he]
      _ = X.map' 0 1 ≫ φ.app 1 := by rw [← Category.assoc, P.head_comp]
      _ = φ.app 0 ≫ X'.map' 0 1 := naturality' φ 0 1
      _ = (φ.app 0 ≫ P'.headToNext) ≫ P'.tail.headToX := by
        rw [Category.assoc, P'.head_comp]
  obtain ⟨a, ha, hδ⟩ := complete_distinguished_triangle_morphism₁
    (Triangle.mk P.headToX P.headToNext P.headConnecting)
    (Triangle.mk P'.headToX P'.headToNext P'.headConnecting)
    P.head_distinguished P'.head_distinguished (φ.app 0) e comm
  refine ⟨homMk (Fin.cases a (fun _ => e)) ?_ ?_ ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ha
    · have hj : j = 0 := Fin.eq_zero j
      subst j
      exact he.symm
  · intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact comm
  · intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hδ

end ExtendsAtLength

end Morphism

set_option backward.isDefEq.respectTransparency false in
/-- Uniform extension of length-two Postnikov-system morphisms would imply uniform existence of
length-three Postnikov systems. -/
@[stacks 0D81 "length-three existence from length-two morphism extension"]
theorem ExistsAtLength.three_of_extends_two
    (h : Morphism.ExtendsAtLength D 2) :
    ExistsAtLength D 3 := by
  intro X hX
  have htail : X.δ₀.IsComplex := ⟨fun i hi => hX.zero (i + 1)⟩
  obtain ⟨P⟩ := two D X.δ₀ htail
  -- The row `X₃ ⟶ 0 ⟶ 0` has a system whose head comparison is the identity.
  -- Extending its map to the tail row supplies the required factorization through `P.head`.
  let R : ComposableArrows D 2 :=
    ComposableArrows.mk₂ (0 : X.obj 0 ⟶ 0) (0 : (0 : D) ⟶ 0)
  let Q₀ : PostnikovSystem R.δ₀.δ₀ := PostnikovSystem.mk₀ (0 : D) (𝟙 _)
  let Q₁ : PostnikovSystem R.δ₀ :=
    mkSucc Q₀ (0 : D) (𝟙 _) 0 0 (contractible_distinguished (0 : D))
      Limits.zero_comp
  let Q : PostnikovSystem R :=
    mkSucc Q₁ (X.obj 0) (𝟙 _) 0 0 (contractible_distinguished (X.obj 0))
      Limits.zero_comp
  let φ : R ⟶ X.δ₀ := ComposableArrows.homMk₂ (X.map' 0 1) 0 0
    (by simpa using (hX.zero 0).symm) (by simp)
  obtain ⟨ψ⟩ := h Q P φ
  have hfactor : ψ.yMap 0 ≫ P.headToX = X.map' 0 1 := by
    have hw := (ψ.comm_toX 0).w
    change (𝟙 (X.obj 0)) ≫ X.map' 0 1 = ψ.yMap 0 ≫ P.headToX at hw
    simpa only [Category.id_comp] using hw.symm
  obtain ⟨Y, toX, connecting, hT⟩ := distinguished_cocone_triangle₁ (ψ.yMap 0)
  exact ⟨mkSucc P Y toX (ψ.yMap 0) connecting hT hfactor⟩

/-- Lemma 13.41.3 (8): for every `n > 2`, existence of Postnikov systems on all complex rows of
length `n` is not a property of all triangulated categories. -/
@[stacks 0D81 "failure of universal finite Postnikov-system existence"]
theorem ExistsAtLength.not_forall_of_two_lt (n : ℕ) (hn : 2 < n) :
    ¬ ∀ {D : Type 1} [Category.{0} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
        [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D],
      ExistsAtLength D n := sorry

namespace Morphism

/-- Lemma 13.41.3 (7): extension of row morphisms between length-two Postnikov systems is not a
property of all triangulated categories. -/
@[stacks 0D81 "failure of universal length-two Postnikov morphism extension"]
theorem ExtendsAtLength.not_forall_two :
    ¬ ∀ {D : Type 1} [Category.{0} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
        [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D],
      ExtendsAtLength D 2 := by
  intro h
  apply ExistsAtLength.not_forall_of_two_lt 3 (by decide)
  intro D _ _ _ _ _ _
  exact ExistsAtLength.three_of_extends_two D (h (D := D))

end Morphism

end PostnikovSystem

end CategoryTheory
