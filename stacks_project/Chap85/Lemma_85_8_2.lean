module

public import ReasLib.CategoryTheory.Sites.Simplicial.SectionsComplex
public import ReasLib.CategoryTheory.Sites.Grothendieck.SectionsComplex
import StacksCheckRecall

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

/- Lemma 85.8.2. The canonical augmented section complex is exact in degrees `-1`
and `0` for every abelian sheaf, and in all degrees for injective coefficients,
in both presentations of a simplicial site. -/
@[stacks 0D77] #check (CategoryTheory.SimplicialSites.globalSectionsExtended_exactAt_negOne_zero C J :
  ∀ (F : Sheaf (topology C J) AddCommGrpCat.{w})
    (n : ℤ) (hn : n = (-1 : ℤ) ∨ n = (0 : ℤ)),
    (globalSectionsExtended C J F).ExactAt n)

#check (CategoryTheory.SimplicialSites.globalSectionsExtended_acyclic_of_injective C J :
  ∀ (F : Sheaf (topology C J) AddCommGrpCat.{w}) [Injective F],
    (globalSectionsExtended C J F).Acyclic)

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

#check (CategoryTheory.Grothendieck.fiberSectionsExtended_exactAt_negOne_zero F J :
  ∀ (G : Sheaf (topology F J) AddCommGrpCat.{w})
    (n : ℤ) (hn : n = (-1 : ℤ) ∨ n = (0 : ℤ)),
    (fiberSectionsExtended F J G).ExactAt n)

#check (CategoryTheory.Grothendieck.fiberSectionsExtended_acyclic_of_injective F J :
  ∀ (G : Sheaf (topology F J) AddCommGrpCat.{w}) [Injective G],
    (fiberSectionsExtended F J G).Acyclic)

end CategoryTheory.Grothendieck
