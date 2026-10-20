module

public import ReasLib.CategoryTheory.Functor.FreeAbelianYoneda
public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelian
public import Mathlib.CategoryTheory.Sites.Adjunction

/-!
# Weak-sheafification free abelian Yoneda API

This leaf owns the Hom/evaluation form of the free abelian Yoneda sheaf
construction. It only requires a weak sheafification adjunction. Additive and
canonical-sections refinements require `HasSheafify` and live in the parent
`FreeAbelianYoneda` leaf.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology.FreeAbelianYoneda

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J AddCommGrpCat.{v}]

/-- The functor obtained by freely abelianizing Yoneda presheaves and then sheafifying. -/
noncomputable abbrev functor : C ⥤ Sheaf J AddCommGrpCat.{v} :=
  yoneda ⋙ J.freeAbelianSheafFunctor

/-- The weak sheafification of the free abelian Yoneda presheaf represented by `U`. -/
@[stacks 03AB "free then sheafify"]
noncomputable abbrev obj (U : C) :
    Sheaf J AddCommGrpCat.{v} :=
  (functor J).obj U

/-- The sheafified free abelian Yoneda morphism induced by `f`. -/
noncomputable abbrev map {U V : C} (f : U ⟶ V) : obj J U ⟶ obj J V :=
  (functor J).map f

/-- Morphisms from the weakly sheafified free abelian representable at `U` to `F` are equivalent
to raw sections of `F` over `U`. -/
@[stacks 03AB "free-then-sheafify evaluation", stacks 05NY]
noncomputable def homEquiv
    (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    (obj J U ⟶ F) ≃ F.obj.obj (op U) :=
  ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F).trans
    (CategoryTheory.FreeAbelianYoneda.homEquiv U F.1)

/-- The weak-sheafification free-abelian-representable Hom/evaluation equivalence commutes with
postcomposition in the target sheaf. -/
theorem homEquiv_comp
    (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (α : obj J U ⟶ F) (f : F ⟶ G) :
    homEquiv J U G (α ≫ f) = f.hom.app (op U) (homEquiv J U F α) := sorry

/-- The weak-sheafification free-abelian-representable Hom/evaluation equivalence commutes with
restriction along a morphism of representing objects. -/
theorem homEquiv_naturality
    {U V : C} (f : U ⟶ V) (F : Sheaf J AddCommGrpCat.{v})
    (α : obj J V ⟶ F) :
    homEquiv J U F (map J f ≫ α) = F.obj.map f.op (homEquiv J V F α) := sorry

/-- The inverse weak-sheafification free-abelian-representable Hom/evaluation equivalence is
natural in the target sheaf. -/
theorem homEquiv_symm_naturality
    (U : C) {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G)
    (s : F.obj.obj (op U)) :
    (homEquiv J U G).symm (f.hom.app (op U) s) =
      (homEquiv J U F).symm s ≫ f := sorry

end CategoryTheory.GrothendieckTopology.FreeAbelianYoneda
