/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.Transport
public import ReasLib.CategoryTheory.Pretriangulated.TriangleMorphism.Uniqueness
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Uniqueness of Morphisms of Finite Postnikov Systems

This leaf records the three independent shifted-Hom vanishing criteria which
make a lift of a morphism of finite rows to a morphism of Postnikov systems
unique.  The criteria are named separately so applications can use the
weakest available hypothesis.
-/

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

namespace PostnikovSystem.Morphism.Uniqueness

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

/-- Vanishing from every noninitial source-row object to the initial auxiliary object of a target
Postnikov system. -/
def Target.vanishing {n : ℕ} (X : ComposableArrows D n)
    {X' : ComposableArrows D n} (P' : PostnikovSystem X') : Prop :=
  ∀ a : Fin n, Subsingleton (ShiftedHom (X.obj a.castSucc) (P' 0) (a.1 : ℤ))

/-- Vanishing from the initial auxiliary object of a source Postnikov system to every noninitial
target-row object. -/
def Source.vanishing {n : ℕ} {X : ComposableArrows D n}
    (P : PostnikovSystem X) (X' : ComposableArrows D n) : Prop :=
  ∀ a : Fin n, Subsingleton (ShiftedHom (P 0) (X'.obj a.succ) (-((a.1 : ℤ) + 1)))

/-- Paired cross-vanishing between two finite rows. -/
def Cross.vanishing {n : ℕ} (X X' : ComposableArrows D n) : Prop :=
  ∀ ⦃a b : Fin (n + 1)⦄, b < a →
    Subsingleton (ShiftedHom (X.obj a) (X'.obj b) ((a.1 : ℤ) - b.1 - 1)) ∧
      Subsingleton (ShiftedHom (X.obj b) (X'.obj a) ((b.1 : ℤ) - a.1))

/-- The disjunction of the three standard uniqueness hypotheses for Postnikov-system
morphisms. -/
@[stacks 0FXE]
def vanishing {n : ℕ} {X X' : ComposableArrows D n}
    (P : PostnikovSystem X) (P' : PostnikovSystem X') : Prop :=
  Target.vanishing X P' ∨ Source.vanishing P X' ∨ Cross.vanishing X X'

end

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D] [IsTriangulated D]

/-- Target-extreme vanishing makes a morphism of Postnikov systems over a fixed row morphism
unique. -/
@[stacks 0FXE]
theorem Target.subsingleton
    {n : ℕ} {X X' : ComposableArrows D n} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X') (h : Target.vanishing X P') :
    Subsingleton (PostnikovSystem.Morphism P P' φ) := sorry

/-- Target-extreme vanishing directly identifies two lifts of the same finite-row morphism,
without installing a local `Subsingleton` instance. -/
@[stacks 0FXE]
theorem Target.eq
    {n : ℕ} {X X' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'} (h : Target.vanishing X P')
    (ψ ψ' : PostnikovSystem.Morphism P P' φ) :
    ψ = ψ' := sorry

/-- Source-extreme vanishing makes a morphism of Postnikov systems over a fixed row morphism
unique. -/
@[stacks 0FXE]
theorem Source.subsingleton
    {n : ℕ} {X X' : ComposableArrows D n} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X') (h : Source.vanishing P X') :
    Subsingleton (PostnikovSystem.Morphism P P' φ) := sorry

/-- Source-extreme vanishing directly identifies two lifts of the same finite-row morphism,
without installing a local `Subsingleton` instance. -/
@[stacks 0FXE]
theorem Source.eq
    {n : ℕ} {X X' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'} (h : Source.vanishing P X')
    (ψ ψ' : PostnikovSystem.Morphism P P' φ) :
    ψ = ψ' := sorry

/-- Cross-vanishing makes a morphism of Postnikov systems over a fixed row morphism unique. -/
@[stacks 0FXE]
theorem Cross.subsingleton
    {n : ℕ} {X X' : ComposableArrows D n} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X') (h : Cross.vanishing X X') :
    Subsingleton (PostnikovSystem.Morphism P P' φ) := sorry

/-- Cross-vanishing directly identifies two lifts of the same finite-row morphism, without
installing a local `Subsingleton` instance. -/
@[stacks 0FXE]
theorem Cross.eq
    {n : ℕ} {X X' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'} (h : Cross.vanishing X X')
    (ψ ψ' : PostnikovSystem.Morphism P P' φ) :
    ψ = ψ' := sorry

/-- Stacks 0FXE, Lemma 13.41.5: any one of the three standard Hom-vanishing hypotheses makes a
morphism of Postnikov systems over a fixed row morphism unique. -/
@[stacks 0FXE]
theorem subsingleton
    {n : ℕ} {X X' : ComposableArrows D n} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X') (h : vanishing P P') :
    Subsingleton (PostnikovSystem.Morphism P P' φ) := sorry

/-- Any standard uniqueness hypothesis directly identifies two lifts of the same finite-row
morphism, without installing a local `Subsingleton` instance. -/
@[stacks 0FXE]
theorem eq
    {n : ℕ} {X X' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ : X ⟶ X'} (h : vanishing P P')
    (ψ ψ' : PostnikovSystem.Morphism P P' φ) :
    ψ = ψ' := sorry

/-- Under any standard uniqueness hypothesis, lifts over propositionally equal finite-row
morphisms agree after transport of the base map. -/
@[stacks 0FXE]
theorem hom_ext
    {n : ℕ} {X X' : ComposableArrows D n} {P : PostnikovSystem X}
    {P' : PostnikovSystem X'} {φ φ' : X ⟶ X'} (h : vanishing P P')
    (hφ : φ = φ') (ψ : PostnikovSystem.Morphism P P' φ)
    (ψ' : PostnikovSystem.Morphism P P' φ') :
    PostnikovSystem.Morphism.changeBase hφ ψ = ψ' := sorry

end

end PostnikovSystem.Morphism.Uniqueness

end CategoryTheory
