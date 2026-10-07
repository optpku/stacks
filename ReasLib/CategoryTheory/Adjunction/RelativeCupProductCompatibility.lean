module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import ReasLib.CategoryTheory.Adjunction.RelativeCupProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Compatibility of relative cup products

This file contains the categorical compatibility statements for the cup-product owner.  The
chapters only specialize these statements to derived categories; no chapter module is imported
here.  The comparison family is explicit because its coherence with the braiding is a genuine
hypothesis, while the cup-product map itself is owned by `Adjunction.relativeDerivedCupProduct`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe uC vC uD vD

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D] [BraidedCategory D]
variable {L : C ⥤ D} {R : D ⥤ C}

/-- The relative cup product commutes with braidings when the supplied pullback-tensor comparison
does.  The statement is phrased as a `CommSq`, so it can be composed with other categorical
compatibility squares without unpacking a chosen equality. -/
@[stacks 0FPM "braided relative cup product"]
theorem relativeDerivedCupProduct_commutative_commSq
    (adj : L ⊣ R)
    (pullbackTensorIso :
      ∀ K M : C,
        L.obj (K ⊗ M) ≅ (L.obj K ⊗ L.obj M))
    (pullbackTensorBraiding :
      ∀ K M : C,
        CommSq
          (pullbackTensorIso K M).hom
          (L.map (β_ K M).hom)
          (β_ (L.obj K) (L.obj M)).hom
          (pullbackTensorIso M K).hom)
    (K M : D) :
    CommSq
      (adj.relativeDerivedCupProduct
        (curriedTensor C) (curriedTensor D)
        (fun A B ↦ (pullbackTensorIso A B).hom) K M)
      (β_ (R.obj K) (R.obj M)).hom
      (R.map (β_ K M).hom)
      (adj.relativeDerivedCupProduct
        (curriedTensor C) (curriedTensor D)
        (fun A B ↦ (pullbackTensorIso A B).hom) M K) := sorry

end CategoryTheory
