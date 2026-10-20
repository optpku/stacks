module

public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Morphisms of localized topoi

An arrow `c : U ⟶ u.obj V` determines a morphism from the topos localized at
`U` to the topos localized at `V`.  The construction only needs continuity of
the induced slice functor, so it is more general than a morphism of sites.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w u₁ u₂ v₁ v₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/-- The morphism of topoi between slice sites induced by a functor `u` and an arrow
`c : U ⟶ u.obj V`. -/
noncomputable def localizedMorphismOfTopoi
    (u : D ⥤ C) {V : D} {U : C} (c : U ⟶ u.obj V)
    [(Over.post u).IsContinuous (JD.over V) (JC.over (u.obj V))]
    [HasWeakSheafify (JC.over (u.obj V)) (Type w)]
    [∀ P : (Over V)ᵒᵖ ⥤ Type w, (Over.post u).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((Over.post u).sheafPullback (Type w) (JD.over V) (JC.over (u.obj V)))]
    [HasSheafify (JC.over U) (Type w)]
    [∀ P : (Over U)ᵒᵖ ⥤ Type w, (Over.map c).op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn (JD.over V) (JC.over U) :=
  MorphismOfTopoiIn.comp
    ((Over.post u).morphismOfTopoiInOfContinuous
      (JD.over V) (JC.over (u.obj V)))
    ((Over.map c).morphismOfTopoiInOfCocontinuous
      (JC.over U) (JC.over (u.obj V)))

end CategoryTheory.Functor
