module

public import ReasLib.Algebra.Category.CommRingCat.FilteredColimit.Algebra
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Etale algebras over filtered colimits

This leaf owns the arbitrary filtered-diagram form of the finite-stage descent
statement for etale algebras.  The neutral cocone-leg algebra structure is
provided by `CommRingCat.FilteredColimit.stageAlgebra`.
-/

open CategoryTheory Limits
open scoped TensorProduct

universe u w uJ vJ

namespace CommRingCat.FilteredColimit.Etale

variable {J : Type vJ} [Category.{uJ} J] [IsFiltered J]

/-- Lemma 10.143.3 (00U2), clause (9): an etale algebra over a filtered
colimit is obtained by base change from an etale algebra at one stage.  The
local `stageAlgebra` instance in the conclusion is the induced scalar
structure required to type the displayed tensor product. -/
@[stacks 00U2 "etale filtered-colimit descent"]
theorem exists_stage
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (B : Type w) [CommRing B] [Algebra c.pt B] [Algebra.Etale c.pt B] :
    ∃ (j : J) (B_j : Type w) (_ : CommRing B_j) (_ : Algebra (F.obj j) B_j),
      letI : Algebra (F.obj j) c.pt := CommRingCat.FilteredColimit.stageAlgebra F c j
      Algebra.Etale (F.obj j) B_j ∧
        Nonempty (B ≃ₐ[c.pt] c.pt ⊗[F.obj j] B_j) := sorry

end CommRingCat.FilteredColimit.Etale
