module

public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Pullback
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Over
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization at a representable sheaf

For `U : C`, sheaves on `(C / U, J.over U)` are compared with objects of `Sh(C, J)` over the
sheafified representable at `U`.  The comparison uses the explicit inverse supplied by
`Functor.SheafifiedRepresentable.pullbackIso`; callers never provide an `IsIso` witness.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v

noncomputable section

namespace CategoryTheory.GrothendieckTopology.RepresentableLocalization

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (U : C)
variable [∀ G : Functor (Over U)ᵒᵖ (Type (max u v)),
  (Over.forget U).op.HasLeftKanExtension G]
variable [HasWeakSheafify (J.over U) (Type (max u v))]
variable [HasWeakSheafify J (Type (max u v))]

/-- The identity-object pullback isomorphism identifying the sheafified representable at `U`
with lower shriek of the terminal sheafified representable on `C / U`. -/
@[stacks 04J3 "identity pullback"]
noncomputable def identityPullbackIso :
    J.sheafifiedRepresentable U ≅
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
        ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))) :=
  Functor.SheafifiedRepresentable.pullbackIso
    (Over.forget U) (J.over U) J (Over.mk (𝟙 U))

/-- The canonical map from localized lower shriek to the sheafified representable at `U`. -/
noncomputable def comparisonHom (G : Sheaf (J.over U) (Type (max u v))) :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj G ⟶
      J.sheafifiedRepresentable U :=
  ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
      ((GrothendieckTopology.SheafifiedRepresentable.Over.mkIdIsTerminal J U).from G) ≫
    (identityPullbackIso J U).inv

/-- The canonical maps from localized lower shriek to the sheafified representable are natural. -/
theorem comparisonHom_naturality
    {G G' : Sheaf (J.over U) (Type (max u v))} (f : G ⟶ G') :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map f ≫
        comparisonHom J U G' =
      comparisonHom J U G := sorry

/-- The canonical comparison from sheaves on `C / U` to sheaves on `C` over the sheafified
representable at `U`. -/
@[stacks 04J3 "representable comparison"]
noncomputable def comparison :
    Functor (Sheaf (J.over U) (Type (max u v))) (Over (J.sheafifiedRepresentable U)) :=
  ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).toOver
    (J.sheafifiedRepresentable U) (comparisonHom J U) (comparisonHom_naturality J U)

namespace comparison

/-- Forgetting the structure morphism from representable localization recovers localization
lower shriek. -/
@[simp]
theorem forget :
    comparison J U ⋙ Over.forget (J.sheafifiedRepresentable U) =
      (Over.forget U).sheafPullback (Type (max u v)) (J.over U) J := sorry

/-- The representable-localization comparison is an equivalence. -/
@[stacks 04J3 "representable equivalence"]
theorem isEquivalence : Functor.IsEquivalence (comparison J U) := sorry

end comparison

end CategoryTheory.GrothendieckTopology.RepresentableLocalization
