/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap73.Definition_73_7_1_FppfCover

/-!
# Čech fibre products of fppf covering families

This leaf owns the iterated fibre products
`V_{σ 0} ×_U ⋯ ×_U V_{σ n}` of an indexed family of morphisms of algebraic
spaces, re-bundled as objects of `Over X`, together with the Čech-descent
predicate on `ObjectProperty (Over X)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.Fppf

/-- Recursive Čech fibre together with its structure morphism to the base. -/
def fibreWithToBase {S : Scheme.{u}} {U : AlgebraicSpace S} {ι : Type v}
    (V : ι → AlgebraicSpace S) (f : ∀ i, V i ⟶ U) (n : ℕ)
    (σ : Fin (n + 1) → ι) : (W : AlgebraicSpace S) × (W ⟶ U) :=
  match n with
  | 0 => ⟨V (σ 0), f (σ 0)⟩
  | n + 1 =>
    let tailHom := (fibreWithToBase V f n (fun k ↦ σ k.succ)).2
    ⟨pullback (f (σ 0)) tailHom, pullback.snd (f (σ 0)) tailHom ≫ tailHom⟩

/-- The Čech fibre product `V_{σ 0} ×_U ⋯ ×_U V_{σ n}`. -/
def fibre {S : Scheme.{u}} {U : AlgebraicSpace S} {ι : Type v}
    (V : ι → AlgebraicSpace S) (f : ∀ i, V i ⟶ U) (n : ℕ)
    (σ : Fin (n + 1) → ι) : AlgebraicSpace S :=
  (fibreWithToBase V f n σ).1

/-- The structure morphism `V_{σ 0} ×_U ⋯ ×_U V_{σ n} ⟶ U`. -/
def fibreToBase {S : Scheme.{u}} {U : AlgebraicSpace S} {ι : Type v}
    (V : ι → AlgebraicSpace S) (f : ∀ i, V i ⟶ U) (n : ℕ)
    (σ : Fin (n + 1) → ι) : fibre V f n σ ⟶ U :=
  (fibreWithToBase V f n σ).2

/-- The degree-zero Čech fibre is the corresponding member of the family. -/
theorem fibre_zero {S : Scheme.{u}} {U : AlgebraicSpace S} {ι : Type v}
    (V : ι → AlgebraicSpace S) (f : ∀ i, V i ⟶ U) (σ : Fin 1 → ι) :
    fibre V f 0 σ = V (σ 0) :=
  sorry

/-- A positive-degree Čech fibre is the pullback of the zeroth member against
the structure morphism of the tail. -/
theorem fibre_succ {S : Scheme.{u}} {U : AlgebraicSpace S} {ι : Type v}
    (V : ι → AlgebraicSpace S) (f : ∀ i, V i ⟶ U) (n : ℕ)
    (σ : Fin (n + 2) → ι) :
    fibre V f (n + 1) σ =
      pullback (f (σ 0)) (fibreToBase V f n (fun k ↦ σ k.succ)) :=
  sorry

/-- The degree-zero structure morphism is the corresponding member of the
family. -/
theorem fibreToBase_zero {S : Scheme.{u}} {U : AlgebraicSpace S} {ι : Type v}
    (V : ι → AlgebraicSpace S) (f : ∀ i, V i ⟶ U) (σ : Fin 1 → ι) :
    fibreToBase V f 0 σ = f (σ 0) :=
  sorry

/-- A positive-degree structure morphism is the composite of `pullback.snd`
with the structure morphism of the tail. -/
theorem fibreToBase_succ {S : Scheme.{u}} {U : AlgebraicSpace S} {ι : Type v}
    (V : ι → AlgebraicSpace S) (f : ∀ i, V i ⟶ U) (n : ℕ)
    (σ : Fin (n + 2) → ι) :
    fibreToBase V f (n + 1) σ =
      pullback.snd (f (σ 0)) (fibreToBase V f n (fun k ↦ σ k.succ)) ≫
        fibreToBase V f n (fun k ↦ σ k.succ) :=
  sorry

/-- The Čech fibre product of a family in `Over X`, as an object of `Over X`. -/
def fibreOver {S : Scheme.{u}} {X : AlgebraicSpace S} {W : Over X} {ι : Type v}
    (V : ι → Over X) (h : ∀ i, V i ⟶ W) (n : ℕ) (σ : Fin (n + 1) → ι) :
    Over X :=
  Over.mk (fibreToBase (fun i ↦ (V i).left) (fun i ↦ (h i).left) n σ ≫ W.hom)

/-- The structure morphism of `fibreOver` is the Čech structure morphism
composed with `W.hom`. -/
theorem fibreOver_hom {S : Scheme.{u}} {X : AlgebraicSpace S} {W : Over X}
    {ι : Type v} (V : ι → Over X) (h : ∀ i, V i ⟶ W) (n : ℕ)
    (σ : Fin (n + 1) → ι) :
    (fibreOver V h n σ).hom =
      fibreToBase (fun i ↦ (V i).left) (fun i ↦ (h i).left) n σ ≫ W.hom :=
  sorry

/-- A property of objects of `Over X` is stable under Čech fibre products of
fppf covering families when it descends from every Čech simplex of such a
family to the base object. -/
def IsStableUnderCech {S : Scheme.{u}} {X : AlgebraicSpace S}
    (P : ObjectProperty (Over X)) : Prop :=
  ∀ {W : Over X} {ι : Type v} (V : ι → Over X) (h : ∀ i, V i ⟶ W)
    [FppfCovering (fun i ↦ (V i).left) (fun i ↦ (h i).left)],
    (∀ (n : ℕ) (σ : Fin (n + 1) → ι), P (fibreOver V h n σ)) → P W

/-- `IsStableUnderCech P` is the implication from `P` on every Čech fibre
product of an fppf covering family `{V i ⟶ W}` to `P W`. -/
theorem isStableUnderCech_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (P : ObjectProperty (Over X)) :
    IsStableUnderCech P ↔
      ∀ {W : Over X} {ι : Type v} (V : ι → Over X) (h : ∀ i, V i ⟶ W),
        FppfCovering (fun i ↦ (V i).left) (fun i ↦ (h i).left) →
          (∀ (n : ℕ) (σ : Fin (n + 1) → ι), P (fibreOver V h n σ)) → P W :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Fppf
