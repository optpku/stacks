module

public import stacks_project.Chap97.«97_6_0_1_Lifting»
public import stacks_project.Chap98.Lemma_98_9_3_FormalObject
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifting formal objects along morphisms formally smooth on objects

If a 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` is
formally smooth on objects, a formal object of the target with a first-stage
fibre lift to the source extends to a formal object of the source with the
same complete local `S`-algebra.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.FormalObject

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X Y : GroupoidsOver S}

/-- Lemma 98.9.3: if `S` is locally Noetherian, `F : X ⟶ Y` is a 1-morphism of
categories fibred in groupoids over `(Sch/S)_fppf` that is formally smooth on
objects, `η` is a formal object of `Y`, and `ξ₁` is an object of `X` with
`F(ξ₁) ≅ η₁`, then there exists a formal object `ξ` of `X` with the same
complete local `S`-algebra as `η` such that `F(ξ) ≅ η`. -/
@[stacks 07X5]
theorem exists_lift (F : X ⟶ Y) [FormallySmoothOnObjects F] (η : FormalObject Y)
    (ξ1 : X.total) (hξ1 : X.p.obj ξ1 = η.base.stageOver 0)
    (e : (toFunctor F).obj ξ1 ≅ η.objects 0)
    (he : Y.p.IsHomLift (𝟙 (η.base.stageOver 0)) e.hom) :
    ∃ ξ : FormalObject X, ξ.base = η.base ∧
      ∃ α : ∀ n, (toFunctor F).obj (ξ.objects n) ≅ η.objects n,
        (∀ n, Y.p.IsHomLift (𝟙 (η.base.stageOver n)) (α n).hom) ∧
          ∀ n, (toFunctor F).map (ξ.step n) ≫ (α (n + 1)).hom =
            (α n).hom ≫ η.step n :=
  sorry

/-- Unpacked same-base fibre-iso data is equivalent to `IsMappedIso F ξ η`. -/
theorem exists_lift_iff (F : X ⟶ Y) (η : FormalObject Y) :
    (∃ ξ : FormalObject X, ξ.base = η.base ∧
        ∃ α : ∀ n, (toFunctor F).obj (ξ.objects n) ≅ η.objects n,
          (∀ n, Y.p.IsHomLift (𝟙 (η.base.stageOver n)) (α n).hom) ∧
            ∀ n, (toFunctor F).map (ξ.step n) ≫ (α (n + 1)).hom =
              (α n).hom ≫ η.step n) ↔
      ∃ ξ : FormalObject X, IsMappedIso F ξ η :=
  sorry

/-- A lift may be chosen so that the first stage is fibre-isomorphic to the given
object `ξ₁` over `Spec(R ⧸ m)`, compatibly with `F(ξ₁) ≅ η₁`. -/
theorem exists_lift_stageOne (F : X ⟶ Y) [FormallySmoothOnObjects F]
    (η : FormalObject Y) (ξ1 : X.total)
    (hξ1 : X.p.obj ξ1 = η.base.stageOver 0)
    (e : (toFunctor F).obj ξ1 ≅ η.objects 0)
    (he : Y.p.IsHomLift (𝟙 (η.base.stageOver 0)) e.hom) :
    ∃ (ξ : FormalObject X) (e0 : ξ.objects 0 ≅ ξ1),
      ξ.base = η.base ∧ X.p.IsHomLift (𝟙 (η.base.stageOver 0)) e0.hom ∧
        ∃ α : ∀ n, (toFunctor F).obj (ξ.objects n) ≅ η.objects n,
          (∀ n, Y.p.IsHomLift (𝟙 (η.base.stageOver n)) (α n).hom) ∧
            (∀ n, (toFunctor F).map (ξ.step n) ≫ (α (n + 1)).hom =
                (α n).hom ≫ η.step n) ∧
              (α 0).hom = (toFunctor F).map e0.hom ≫ e.hom :=
  sorry

end AlgebraicGeometry.GroupoidsOver.FormalObject
