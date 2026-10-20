module

public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelianYoneda.Weak
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Sheafified free abelian Yoneda presheaves

This leaf treats the additive canonical-sections refinement of the sheafification of the free
abelian Yoneda presheaf. The weaker Hom/evaluation API is owned by `FreeAbelianYoneda.Weak`.
Both are distinct from freely abelianizing an already sheafified representable, which has
different hypotheses and is owned by `FreeAbelianRepresentable`.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology.FreeAbelianYoneda

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{v}]

/-- Morphisms from the sheafified free abelian representable at `U` identify additively with raw
sections over `U`. -/
@[stacks 03AB "additive free-then-sheafify evaluation"]
noncomputable def homAddEquiv
    (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    (obj J U ⟶ F) ≃+ F.obj.obj (op U) :=
  ((sheafificationAdjunction J AddCommGrpCat.{v}).homAddEquiv _ F).trans
    (CategoryTheory.FreeAbelianYoneda.homAddEquiv U F.1)

/-- The additive free-abelian-representable Hom/evaluation equivalence commutes with
postcomposition in the target sheaf. -/
theorem homAddEquiv_comp
    (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (α : obj J U ⟶ F) (f : F ⟶ G) :
    homAddEquiv J U G (α ≫ f) = f.hom.app (op U) (homAddEquiv J U F α) := sorry

/-- The additive free-abelian-representable Hom/evaluation equivalence commutes with restriction
along a morphism of representing objects. -/
theorem homAddEquiv_naturality
    {U V : C} (f : U ⟶ V) (F : Sheaf J AddCommGrpCat.{v})
    (α : obj J V ⟶ F) :
    homAddEquiv J U F (map J f ≫ α) = F.obj.map f.op (homAddEquiv J V F α) := sorry

/-- The inverse additive free-abelian-representable Hom/evaluation equivalence is natural in the
target sheaf. -/
theorem homAddEquiv_symm_naturality
    (U : C) {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G)
    (s : F.obj.obj (op U)) :
    (homAddEquiv J U G).symm (f.hom.app (op U) s) =
      (homAddEquiv J U F).symm s ≫ f := sorry

/-- Morphisms from the sheafified free abelian representable at `U` identify additively with
sections over `U`. -/
noncomputable def homSectionsEquiv
    (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    (obj J U ⟶ F) ≃+
      ((sheafSections J AddCommGrpCat.{v}).obj (op U)).obj F :=
  (homAddEquiv J U F).trans
    ((sheafSectionsNatIsoEvaluation
      (J := J) (A := AddCommGrpCat.{v}) (X := U)).app F).symm.addCommGroupIsoToAddEquiv

/-- Sections over `U` identify additively with morphisms from the sheafified free abelian
representable at `U`. -/
noncomputable abbrev sectionsHomEquiv
    (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    ((sheafSections J AddCommGrpCat.{v}).obj (op U)).obj F ≃+
      (obj J U ⟶ F) :=
  (homSectionsEquiv J U F).symm

/-- The sheafified free-abelian-representable Hom/sections equivalence commutes with
postcomposition in the target sheaf. -/
theorem homSectionsEquiv_comp
    (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (α : obj J U ⟶ F) (f : F ⟶ G) :
    homSectionsEquiv J U G (α ≫ f) =
      ((sheafSections J AddCommGrpCat.{v}).obj (op U)).map f
        (homSectionsEquiv J U F α) := sorry

/-- The sections-to-Hom additive equivalence for the sheafified free abelian representable is
natural in the target sheaf. -/
theorem sectionsHomEquiv_naturality
    (U : C) {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G)
    (s : ((sheafSections J AddCommGrpCat.{v}).obj (op U)).obj F) :
    sectionsHomEquiv J U G
        (((sheafSections J AddCommGrpCat.{v}).obj (op U)).map f s) =
      sectionsHomEquiv J U F s ≫ f := sorry

end CategoryTheory.GrothendieckTopology.FreeAbelianYoneda
