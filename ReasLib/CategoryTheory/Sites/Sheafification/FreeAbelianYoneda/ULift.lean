module

public import ReasLib.CategoryTheory.Functor.FreeAbelianYoneda.ULift
public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelian
public import Mathlib.CategoryTheory.Sites.Adjunction

/-!
# Universe-raised free abelian Yoneda sheaves

This leaf sheafifies the universe-raised free abelian Yoneda presheaf. It is the large-value
counterpart of `FreeAbelianYoneda.Weak` and keeps the site hom universe independent from the
universe in which the abelian sheaves take values.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe w v u

namespace CategoryTheory.GrothendieckTopology.FreeAbelianYoneda.ULift

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J AddCommGrpCat.{max w v}]

/-- The universe-raised free abelian Yoneda functor followed by sheafification. -/
noncomputable abbrev functor : C ⥤ Sheaf J AddCommGrpCat.{max w v} :=
  CategoryTheory.FreeAbelianYoneda.ULift.functor.{u, v, w} ⋙
    presheafToSheaf J AddCommGrpCat.{max w v}

/-- The sheafification of the universe-raised free abelian representable at `U`. -/
@[stacks 03AB "universe-raised free then sheafify"]
noncomputable abbrev obj (U : C) : Sheaf J AddCommGrpCat.{max w v} :=
  (functor.{w} J).obj U

/-- The sheafified universe-raised free abelian Yoneda morphism induced by `f`. -/
noncomputable abbrev map {U V : C} (f : U ⟶ V) : obj.{w} J U ⟶ obj J V :=
  (functor.{w} J).map f

/-- Morphisms from the sheafified universe-raised free abelian representable at `U` are
equivalent to sections over `U`. -/
@[stacks 03AB "universe-raised evaluation", stacks 05NY "universe-raised"]
noncomputable def homEquiv {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{max w v}]
    (U : C) (F : Sheaf J AddCommGrpCat.{max w v}) :
    (obj.{w} J U ⟶ F) ≃ F.obj.obj (op U) :=
  ((sheafificationAdjunction J AddCommGrpCat.{max w v}).homEquiv _ F).trans
    (CategoryTheory.FreeAbelianYoneda.ULift.homEquiv U F.1)

/-- The universe-raised Hom/evaluation equivalence commutes with postcomposition. -/
theorem homEquiv_comp (U : C) {F G : Sheaf J AddCommGrpCat.{max w v}}
    (α : obj.{w} J U ⟶ F) (f : F ⟶ G) :
    homEquiv U G (α ≫ f) = f.hom.app (op U) (homEquiv U F α) := sorry

/-- The universe-raised Hom/evaluation equivalence commutes with restriction in the
representing object. -/
theorem homEquiv_naturality {U V : C} (f : U ⟶ V)
    (F : Sheaf J AddCommGrpCat.{max w v}) (α : obj.{w} J V ⟶ F) :
    homEquiv U F (map J f ≫ α) = F.obj.map f.op (homEquiv V F α) := sorry

/-- The inverse universe-raised Hom/evaluation equivalence is natural in the target sheaf. -/
theorem homEquiv_symm_naturality (U : C) {F G : Sheaf J AddCommGrpCat.{max w v}}
    (f : F ⟶ G) (s : F.obj.obj (op U)) :
    (homEquiv U G).symm (f.hom.app (op U) s) = (homEquiv U F).symm s ≫ f := sorry

end CategoryTheory.GrothendieckTopology.FreeAbelianYoneda.ULift
