/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CompleteLocalAlgebra.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Formal objects over schemes

Formal objects are forward systems over the positive maximal-adic quotients
of Noetherian complete local algebras with finite-type residue field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry

namespace GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

/-- A complete local base with a forward system in a groupoid fibration over
its positive maximal-adic quotient spectra. -/
def FormalObject (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, v} (Over S)) :=
  Σ' base : CompleteLocalSAlgebra S,
    Σ' objects : ℕ → X.total,
      Σ' step : ∀ n, objects n ⟶ objects (n + 1),
        (∀ n, X.p.obj (objects n) = base.stageOver n) ∧
          ∀ n, X.p.IsHomLift (base.stageHom n) (step n)

namespace FormalObject

variable {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, v} (Over S)}

/-- The complete local base of a formal object. -/
def base (ξ : FormalObject X) : CompleteLocalSAlgebra S := ξ.1

/-- The objects at the positive maximal-adic stages. -/
def objects (ξ : FormalObject X) : ℕ → X.total := ξ.2.1

/-- The successor transition morphisms of a formal object. -/
def step (ξ : FormalObject X) (n : ℕ) : ξ.objects n ⟶ ξ.objects (n + 1) := ξ.2.2.1 n

/-- Each stage lies over the corresponding truncated spectrum. -/
def over_obj (ξ : FormalObject X) (n : ℕ) :
    X.p.obj (ξ.objects n) = ξ.base.stageOver n := ξ.2.2.2.1 n

/-- Each successor transition lifts the canonical truncation map. -/
def over_step (ξ : FormalObject X) (n : ℕ) :
    X.p.IsHomLift (ξ.base.stageHom n) (ξ.step n) := ξ.2.2.2.2 n

/-- The functor on the ordered natural numbers determined by the stages and transitions. -/
def toFunctor (ξ : FormalObject X) : ℕ ⥤ X.total := Functor.ofSequence ξ.step


/-- Package a complete local `S`-algebra and a compatible forward system as a formal
object of `X`. -/
def of (base : CompleteLocalSAlgebra S) (objects : ℕ → X.total)
    (step : ∀ n, objects n ⟶ objects (n + 1))
    (over_obj : ∀ n, X.p.obj (objects n) = base.stageOver n)
    (over_step : ∀ n, X.p.IsHomLift (base.stageHom n) (step n)) :
    FormalObject X :=
  ⟨base, objects, step, over_obj, over_step⟩

/-- The packaged formal object recovers the supplied complete local `S`-algebra. -/
theorem of_base (base : CompleteLocalSAlgebra S) (objects : ℕ → X.total)
    (step : ∀ n, objects n ⟶ objects (n + 1))
    (over_obj : ∀ n, X.p.obj (objects n) = base.stageOver n)
    (over_step : ∀ n, X.p.IsHomLift (base.stageHom n) (step n)) :
    (of base objects step over_obj over_step).base = base := rfl

/-- Stagewise specification of a formal object over the truncations of its base. -/
theorem spec (ξ : FormalObject X) (n : ℕ) :
    X.p.obj (ξ.objects n) = ξ.base.stageOver n ∧
      X.p.IsHomLift (ξ.base.stageHom n) (ξ.step n) := ⟨ξ.over_obj n, ξ.over_step n⟩

/-- The stagewise over-object and over-step conditions are equivalent to the
bundled pair of universal conditions. -/
theorem spec_iff (ξ : FormalObject X) :
    (∀ n, X.p.obj (ξ.objects n) = ξ.base.stageOver n ∧
        X.p.IsHomLift (ξ.base.stageHom n) (ξ.step n)) ↔
      ((∀ n, X.p.obj (ξ.objects n) = ξ.base.stageOver n) ∧
        ∀ n, X.p.IsHomLift (ξ.base.stageHom n) (ξ.step n)) := by
  constructor
  · intro h
    exact ⟨fun n ↦ (h n).1, fun n ↦ (h n).2⟩
  · rintro ⟨hobj, hstep⟩ n
    exact ⟨hobj n, hstep n⟩

/-- The residue-stage object `ξ₁`, lying over `Spec(R ⧸ m)`. -/
def stageOne (ξ : FormalObject X) : X.total :=
  ξ.objects 0

/-- The first stage of a formal object lies over `Spec(R ⧸ m) ⟶ S`. -/
theorem stageOne_over (ξ : FormalObject X) :
    X.p.obj ξ.stageOne = ξ.base.stageOver 0 := ξ.over_obj 0

variable {Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, v} (Over S)}

/-- The image `F(ξ)` of a formal object along a 1-morphism of categories fibred in
groupoids: the same complete local base, with stages and transitions mapped by `F`. -/
def map (F : X ⟶ Y) (ξ : FormalObject X) : FormalObject Y :=
  ⟨ξ.base, (fun n ↦ (FiberedCategoryOver.Groupoids.toFunctor F).obj (ξ.objects n)),
    (fun n ↦ (FiberedCategoryOver.Groupoids.toFunctor F).map (ξ.step n)), sorry⟩

/-- Mapping a formal object along `F` preserves the complete local base. -/
theorem map_base (F : X ⟶ Y) (ξ : FormalObject X) :
    (map F ξ).base = ξ.base := rfl

/-- Stage `n` of `F(ξ)` is the image of the original stage under `F`. -/
theorem map_objects (F : X ⟶ Y) (ξ : FormalObject X) (n : ℕ) :
    (map F ξ).objects n = (FiberedCategoryOver.Groupoids.toFunctor F).obj (ξ.objects n) := rfl

/-- Successor transitions of `F(ξ)` are the images of the original transitions under
`F`. -/
theorem map_step (F : X ⟶ Y) (ξ : FormalObject X) (n : ℕ) :
    (map F ξ).step n = (FiberedCategoryOver.Groupoids.toFunctor F).map (ξ.step n) := rfl

/-- Unpacked meaning of `F(ξ) ≅ η`: the same complete local `S`-algebra, together with
a natural family of fibre isomorphisms over identities on the truncations. -/
def IsMappedIso (F : X ⟶ Y) (ξ : FormalObject X) (η : FormalObject Y) : Prop :=
  ξ.base = η.base ∧
    ∃ α : ∀ n, (FiberedCategoryOver.Groupoids.toFunctor F).obj (ξ.objects n) ≅ η.objects n,
      (∀ n, Y.p.IsHomLift (𝟙 (η.base.stageOver n)) (α n).hom) ∧
        ∀ n, (FiberedCategoryOver.Groupoids.toFunctor F).map (ξ.step n) ≫ (α (n + 1)).hom =
          (α n).hom ≫ η.step n

/-- `IsMappedIso F ξ η` is the same-base condition together with a natural family of
fibre isomorphisms `F(ξ_n) ≅ η_n`. -/
theorem isMappedIso_iff (F : X ⟶ Y) (ξ : FormalObject X) (η : FormalObject Y) :
    IsMappedIso F ξ η ↔
      ξ.base = η.base ∧
        ∃ α : ∀ n, (map F ξ).objects n ≅ η.objects n,
          (∀ n, Y.p.IsHomLift (𝟙 (η.base.stageOver n)) (α n).hom) ∧
            ∀ n, (map F ξ).step n ≫ (α (n + 1)).hom = (α n).hom ≫ η.step n :=
  Iff.rfl

end FormalObject

end GroupoidsOver

end AlgebraicGeometry

