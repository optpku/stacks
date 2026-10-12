/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_3_5
public import stacks_project.Chap85.Lemma_85_8_2_Complex
public import stacks_project.Chap85.Lemma_85_8_2_Fiberwise

/-!
# Lemma 85.8.2

In Situation 85.3.3, an abelian sheaf `F` on `C_total` has a canonical cochain
complex `0 → Γ(C_total, F) → Γ(C_0, F_0) → Γ(C_1, F_1) → ⋯`, obtained by
applying `Hom(-, F)` to the resolution of Lemma 85.8.1. It is exact in source
degrees `-1` and `0`, and exact in every degree if `F` is injective.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology HomologicalComplex Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [∀ n, (ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget AddCommGrpCat.{w})]

/-- Lemma 85.8.2 (1): in Situation 85.3.3 case A, let `F` be an abelian sheaf on
`C_total`. The canonical complex
`0 → Γ(C_total, F) → Γ(C_0, F_0) → Γ(C_1, F_1) → ⋯` is exact in degrees
`-1` and `0`. -/
@[stacks 0D77]
theorem globalSectionsExtended_exactAt_negOne_zero
    (F : Sheaf (topology C J) AddCommGrpCat.{w})
    (n : ℤ) (hn : n = (-1 : ℤ) ∨ n = (0 : ℤ)) :
    (globalSectionsExtended C J F).ExactAt n :=
  sorry

/-- Lemma 85.8.2 (2): in Situation 85.3.3 case A, if `F` is injective then the
canonical complex `0 → Γ(C_total, F) → Γ(C_0, F_0) → Γ(C_1, F_1) → ⋯` is exact
in every degree. -/
@[stacks 0D77]
theorem globalSectionsExtended_acyclic_of_injective
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) [Injective F] :
    (globalSectionsExtended C J F).Acyclic :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj n)ᵒᵖ ⥤ Type w, (ι F n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/-- Lemma 85.8.2 (3): in Situation 85.3.3 case B, let `G` be an abelian sheaf on
`C_total`. The canonical complex
`0 → Γ(C_total, G) → Γ(C_0, G_0) → Γ(C_1, G_1) → ⋯` is exact in degrees
`-1` and `0`. -/
@[stacks 0D77]
theorem fiberSectionsExtended_exactAt_negOne_zero
    (G : Sheaf (topology F J) AddCommGrpCat.{w})
    (n : ℤ) (hn : n = (-1 : ℤ) ∨ n = (0 : ℤ)) :
    (fiberSectionsExtended F J G).ExactAt n :=
  sorry

/-- Lemma 85.8.2 (4): in Situation 85.3.3 case B, if `G` is injective then the
canonical complex `0 → Γ(C_total, G) → Γ(C_0, G_0) → Γ(C_1, G_1) → ⋯` is exact
in every degree. -/
@[stacks 0D77]
theorem fiberSectionsExtended_acyclic_of_injective
    (G : Sheaf (topology F J) AddCommGrpCat.{w}) [Injective G] :
    (fiberSectionsExtended F J G).Acyclic :=
  sorry

end CategoryTheory.Grothendieck
