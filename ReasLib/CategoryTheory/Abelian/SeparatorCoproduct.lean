module

public import Mathlib.SetTheory.Cardinal.Basic
public import ReasLib.CategoryTheory.Subobject.Image

/-!
# Coproduct Presentations from Proper-Subobject Tests

This leaf turns the standard test that every proper subobject misses a map from
`U` into an epimorphic presentation by a coproduct of copies of `U`.  The
assumption is deliberately stated directly, so users may supply a separator,
a generating family, or another source of the test without imposing a chosen
generator API.
-/

@[expose] public section

open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {U M : C}

/-- The coproduct map obtained by choosing, for every proper subobject of `M`, a map from `U`
which does not factor through it. -/
noncomputable def coproductMapOfProperSubobjectTest
    [HasCoproduct fun _ : Subobject M ↦ U]
    (hU : ∀ (N : Subobject M), N ≠ ⊤ → ∃ f : U ⟶ M, ¬ N.Factors f) :
    (∐ fun _ : Subobject M ↦ U) ⟶ M :=
  Sigma.desc fun N ↦
    @dite (U ⟶ M) (N = ⊤) (Classical.propDecidable _)
      (fun _ ↦ 0)
      (fun hN ↦ Classical.choose (hU N hN))

/-- The component of `coproductMapOfProperSubobjectTest` indexed by a subobject is its chosen
test morphism, or zero at the top subobject. -/
@[simp] theorem coproductMapOfProperSubobjectTest_ι
    [HasCoproduct fun _ : Subobject M ↦ U]
    (hU : ∀ (N : Subobject M), N ≠ ⊤ → ∃ f : U ⟶ M, ¬ N.Factors f)
    (N : Subobject M) :
    Sigma.ι (fun _ : Subobject M ↦ U) N ≫ coproductMapOfProperSubobjectTest hU =
      @dite (U ⟶ M) (N = ⊤) (Classical.propDecidable _)
        (fun _ ↦ 0)
        (fun hN ↦ Classical.choose (hU N hN)) := sorry

/-- The chosen coproduct map from a proper-subobject test is epic. -/
theorem epi_coproductMapOfProperSubobjectTest
    [HasCoproduct fun _ : Subobject M ↦ U]
    (hU : ∀ (N : Subobject M), N ≠ ⊤ → ∃ f : U ⟶ M, ¬ N.Factors f) :
    Epi (coproductMapOfProperSubobjectTest hU) := sorry

/-- The coproduct map obtained from a proper-subobject test after shrinking the subobject
lattice to a chosen small model. -/
noncomputable def coproductMapOfProperSubobjectTestShrink
    [Small.{w} (Subobject M)]
    [HasCoproduct fun _ : Shrink.{w} (Subobject M) ↦ U]
    (hU : ∀ (N : Subobject M), N ≠ ⊤ → ∃ f : U ⟶ M, ¬ N.Factors f) :
    (∐ fun _ : Shrink.{w} (Subobject M) ↦ U) ⟶ M :=
  Sigma.desc fun i ↦
    let N : Subobject M := (equivShrink (Subobject M)).symm i
    @dite (U ⟶ M) (N = ⊤) (Classical.propDecidable _)
      (fun _ ↦ 0)
      (fun hN ↦ Classical.choose (hU N hN))

/-- The component of `coproductMapOfProperSubobjectTestShrink` is the selected test map for
the corresponding original subobject. -/
@[simp] theorem coproductMapOfProperSubobjectTestShrink_ι
    [Small.{w} (Subobject M)]
    [HasCoproduct fun _ : Shrink.{w} (Subobject M) ↦ U]
    (hU : ∀ (N : Subobject M), N ≠ ⊤ → ∃ f : U ⟶ M, ¬ N.Factors f)
    (i : Shrink.{w} (Subobject M)) :
    Sigma.ι (fun _ : Shrink.{w} (Subobject M) ↦ U) i ≫
        coproductMapOfProperSubobjectTestShrink hU =
      let N : Subobject M := (equivShrink (Subobject M)).symm i
      @dite (U ⟶ M) (N = ⊤) (Classical.propDecidable _)
        (fun _ ↦ 0)
        (fun hN ↦ Classical.choose (hU N hN)) := sorry

/-- The chosen shrink-indexed coproduct map from a proper-subobject test is epic. -/
theorem epi_coproductMapOfProperSubobjectTestShrink
    [Small.{w} (Subobject M)]
    [HasCoproduct fun _ : Shrink.{w} (Subobject M) ↦ U]
    (hU : ∀ (N : Subobject M), N ≠ ⊤ → ∃ f : U ⟶ M, ¬ N.Factors f) :
    Epi (coproductMapOfProperSubobjectTestShrink hU) := sorry

/-- A proper-subobject test indexed by a small model of `Subobject M` produces an epimorphism
from a coproduct of copies of `U` onto `M`. -/
theorem exists_epi_from_coproduct_of_properSubobject_test_shrink
    [Small.{w} (Subobject M)]
    [HasCoproduct fun _ : Shrink.{w} (Subobject M) ↦ U]
    (hU : ∀ (N : Subobject M), N ≠ ⊤ → ∃ f : U ⟶ M, ¬ N.Factors f) :
    ∃ f : (∐ fun _ : Shrink.{w} (Subobject M) ↦ U) ⟶ M, Epi f := sorry

/-- A proper-subobject test produces an epimorphism from the coproduct indexed by the full
subobject lattice. -/
theorem exists_epi_from_coproduct_of_properSubobject_test
    [HasCoproducts.{max u v} C]
    (hU : ∀ (N : Subobject M), N ≠ ⊤ → ∃ f : U ⟶ M, ¬ N.Factors f) :
    ∃ f : (∐ fun _ : Subobject M ↦ U) ⟶ M, Epi f := sorry

/-- If the subobject lattice of `M` has cardinality at most `κ`, a proper-subobject test
produces an epimorphism from at most `κ` copies of `U`. -/
theorem exists_epi_from_coproduct_of_properSubobject_test_cardinal_le
    [HasCoproducts.{max u v} C]
    (hU : ∀ (N : Subobject M), N ≠ ⊤ → ∃ f : U ⟶ M, ¬ N.Factors f)
    (κ : Cardinal.{max u v}) (hM : Cardinal.mk (Subobject M) ≤ κ) :
    ∃ (ι : Type (max u v)) (_ : Cardinal.mk ι ≤ κ)
      (f : (∐ fun _ : ι ↦ U) ⟶ M), Epi f := sorry

end CategoryTheory
