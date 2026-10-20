module

public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
public import ReasLib.CategoryTheory.Monoidal.Closed.TensorInternalHom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Source-order internal-Hom maps

This leaf owns the source-order maps that repeatedly occur for internal-Hom complexes.  The
construction only uses a braided closed monoidal category, so it applies to ordinary complexes,
derived categories, module categories, and any other closed monoidal model.  Ringed-site and
ringed-space chapters should specialize these maps instead of owning parallel copies.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace CategoryTheory.MonoidalClosed.Source

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [BraidedCategory C] [MonoidalClosed C]

/-- Source-order composition of internal Homs. -/
@[stacks 0A8V, stacks 0A91 "source-order internal-Hom composition"]
noncomputable def comp (K L M : C) :
    (ihom L).obj M ⊗ (ihom K).obj L ⟶ (ihom K).obj M :=
  (β_ ((ihom L).obj M) ((ihom K).obj L)).hom ≫ MonoidalClosed.comp K L M

/-- The source-order composition map is the braided transport of closed composition. -/
theorem comp_spec (K L M : C) :
    comp K L M =
      (β_ ((ihom L).obj M) ((ihom K).obj L)).hom ≫ MonoidalClosed.comp K L M := sorry

/-- Source-order internal-Hom composition is covariantly natural in its target. -/
@[stacks 0A8V "source-order composition target naturality"]
theorem comp_natural_target
    (K L : C) {M₁ M₂ : C} (f : M₁ ⟶ M₂) :
    CommSq
      (((ihom L).map f) ⊗ₘ 𝟙 ((ihom K).obj L))
      (comp K L M₁)
      (comp K L M₂)
      ((ihom K).map f) := sorry

/-- Equality form of `comp_natural_target`. -/
@[stacks 0A8V "source-order composition target naturality equation"]
theorem comp_natural_target_assoc
    (K L : C) {M₁ M₂ : C} (f : M₁ ⟶ M₂) :
    (((ihom L).map f) ⊗ₘ 𝟙 ((ihom K).obj L)) ≫ comp K L M₂ =
      comp K L M₁ ≫ (ihom K).map f := sorry

/-- Source-order internal-Hom composition is contravariantly natural in its source. -/
@[stacks 0A8V "source-order composition source naturality"]
theorem comp_natural_source
    {K K' L M : C} (f : K ⟶ K') :
    CommSq
      (𝟙 ((ihom L).obj M) ⊗ₘ (pre f).app L)
      (comp K' L M)
      (comp K L M)
      ((pre f).app M) := sorry

/-- Equality form of `comp_natural_source`. -/
@[stacks 0A8V "source-order composition source naturality equation"]
theorem comp_natural_source_assoc
    {K K' L M : C} (f : K ⟶ K') :
    (𝟙 ((ihom L).obj M) ⊗ₘ (pre f).app L) ≫ comp K L M =
      comp K' L M ≫ (pre f).app M := sorry

/-- The middle variable has opposite variance on the two internal-Hom factors, so its canonical
statement is the equality of the two source-order composites rather than a single square. -/
@[stacks 0A8V "source-order composition middle naturality"]
theorem comp_natural_middle
    (K : C) {L L' M : C} (g : L ⟶ L') :
    ((pre g).app M ⊗ₘ 𝟙 ((ihom K).obj L)) ≫ comp K L M =
      (𝟙 ((ihom L').obj M) ⊗ₘ (ihom K).map g) ≫ comp K L' M := sorry

/-- The tensor/internal-Hom comparison in source order. -/
@[stacks 0BYT "source-order tensor/internal-Hom comparison"]
noncomputable abbrev tensor (K L M : C) :
    K ⊗ (ihom M).obj L ⟶ (ihom M).obj (K ⊗ L) :=
  MonoidalClosed.tensorInternalHomComparison K L M

/-- The source-order tensor/internal-Hom comparison after uncurrying. -/
theorem tensor_spec (K L M : C) :
    uncurry (tensor K L M) =
      (α_ M K ((ihom M).obj L)).inv ≫
        (β_ M K).hom ▷ (ihom M).obj L ≫
          (α_ K M ((ihom M).obj L)).hom ≫ K ◁ (ihom.ev M).app L := sorry

namespace Iterated

/-- The tensor-side evaluation map whose transpose gives the iterated internal-Hom map. -/
noncomputable def side (K L M : C) :
    (((ihom L).obj M) ⊗ K) ⊗ (ihom K).obj L ⟶ M :=
  (β_ (((ihom L).obj M) ⊗ K) ((ihom K).obj L)).hom ≫
    (α_ ((ihom K).obj L) ((ihom L).obj M) K).inv ≫
      ((β_ ((ihom K).obj L) ((ihom L).obj M)).hom ▷ K) ≫
        comp K L M ▷ K ≫
          (β_ ((ihom K).obj M) K).hom ≫
            uncurry (𝟙 ((ihom K).obj M))

/-- The tensor-to-iterated-internal-Hom comparison. -/
@[stacks 0A67, stacks 0A8U, stacks 0A92 "source-order tensor-to-iterated internal-Hom comparison"]
noncomputable def map (K L M : C) :
    (ihom L).obj M ⊗ K ⟶ (ihom ((ihom K).obj L)).obj M :=
  braidedHomEquiv ((ihom L).obj M ⊗ K) ((ihom K).obj L) M (side K L M)

/-- The iterated internal-Hom map is characterized by its tensor-side transpose. -/
theorem map_spec (K L M : C) :
    (braidedHomEquiv ((ihom L).obj M ⊗ K) ((ihom K).obj L) M).symm
        (map K L M) = side K L M := sorry

/-- Uncurrying the iterated internal-Hom map gives its evaluation composite. -/
theorem map_uncurry (K L M : C) :
    uncurry (map K L M) =
      (α_ ((ihom K).obj L) ((ihom L).obj M) K).inv ≫
        ((β_ ((ihom K).obj L) ((ihom L).obj M)).hom ▷ K) ≫
          comp K L M ▷ K ≫
            (β_ ((ihom K).obj M) K).hom ≫
              uncurry (𝟙 ((ihom K).obj M)) := sorry

end Iterated

/-- The canonical internal-Hom morphism induced contravariantly by `f` and covariantly by `g`. -/
@[stacks 0A95 "internal-Hom map"]
noncomputable def map
    {L' L I' I : C} (f : L' ⟶ L) (g : I' ⟶ I) :
    (ihom L).obj I' ⟶ (ihom L').obj I :=
  (ihom L).map g ≫ (MonoidalClosed.pre f).app I

/-- The internal-Hom map unfolds to postcomposition followed by precomposition. -/
theorem map_spec
    {L' L I' I : C} (f : L' ⟶ L) (g : I' ⟶ I) :
    map f g = (ihom L).map g ≫ (MonoidalClosed.pre f).app I := sorry

end CategoryTheory.MonoidalClosed.Source

end
