module

public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Sites.Over.Derived.Square
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Unbounded derived base change on slice sites

The canonical base-change map is the right mate of the derived pullback square.  It exists for a
commutative square.  Guitart exactness, and hence cartesianity, makes it invertible.
-/

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology.Derived.Over.BaseChange

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable {X' X Y' Y : C}
variable (i : X' ⟶ X) (p : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
variable [HasSheafify (J.over X') AddCommGrpCat.{max u v}]
variable [HasSheafify (J.over X) AddCommGrpCat.{max u v}]
variable [HasSheafify (J.over Y') AddCommGrpCat.{max u v}]
variable [HasSheafify (J.over Y) AddCommGrpCat.{max u v}]
variable [∀ P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v},
  (Over.map f).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Over X')ᵒᵖ ⥤ AddCommGrpCat.{max u v},
  (Over.map p).op.HasPointwiseRightKanExtension P]

/-- The derived base-change transformation for a commutative square of slice sites. -/
@[stacks 02N8 "derived base-change map on slice sites"]
noncomputable def map (hcomm : i ≫ f = p ≫ g) :
    Over.pushforward J f ⋙ Over.pullback J g ⟶
      Over.pullback J i ⋙ Over.pushforward J p :=
  CategoryTheory.DerivedBaseChange.map
    (Over.adjunction J f) (Over.adjunction J p)
    (Pullback.squareIso J i p f g hcomm)

/-- The mate-equation predicate characterizing the derived slice-site base-change map. -/
@[stacks 02N8 "derived slice base-change specification"]
abbrev IsMap (hcomm : i ≫ f = p ≫ g)
    (η : Over.pushforward J f ⋙ Over.pullback J g ⟶
      Over.pullback J i ⋙ Over.pushforward J p) : Prop :=
  CategoryTheory.DerivedBaseChange.IsMap
    (Over.adjunction J f) (Over.adjunction J p)
    (Pullback.squareIso J i p f g hcomm) η

/-- The canonical derived slice-site base-change transformation satisfies its mate equation. -/
@[stacks 02N8 "derived slice base-change specification"]
theorem map_isMap (hcomm : i ≫ f = p ≫ g) :
    IsMap J i p f g hcomm (map J i p f g hcomm) := sorry

/-- The component of the derived slice-site base-change transformation at a derived object. -/
@[stacks 02N8 "derived slice base-change component"]
noncomputable abbrev app (hcomm : i ≫ f = p ≫ g)
    (K : DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max u v})) :
    (Over.pullback J g).obj ((Over.pushforward J f).obj K) ⟶
      (Over.pushforward J p).obj ((Over.pullback J i).obj K) :=
  (map J i p f g hcomm).app K

/-- The component of the derived slice-site base-change map is characterized by the adjunction
transpose formula. -/
@[stacks 02N8 "derived slice base-change component specification"]
theorem app_spec (hcomm : i ≫ f = p ≫ g)
    (K : DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max u v})) :
    (((Over.adjunction J p).homEquiv
        ((Over.pullback J g).obj ((Over.pushforward J f).obj K))
        ((Over.pullback J i).obj K)).symm (app J i p f g hcomm K)) =
      (Pullback.squareIso J i p f g hcomm).hom.app ((Over.pushforward J f).obj K) ≫
        (Over.pullback J i).map ((Over.adjunction J f).counit.app K) := sorry

/-- Guitart exactness makes the derived slice-site base-change transformation invertible. -/
@[stacks 0EYV "Guitart-exact derived base change"]
theorem map_isIso_of_guitartExact (hcomm : i ≫ f = p ≫ g)
    (hsq : TwoSquare.GuitartExact (Over.mapCommSq i p f g hcomm).iso.hom) :
    IsIso (map J i p f g hcomm) := sorry

/-- Cartesianity makes the derived slice-site base-change transformation invertible. -/
@[stacks 0EZ0 "derived base change for a cartesian slice square", instance]
noncomputable instance map_isIso (hcart : IsPullback i p f g) :
    IsIso (map J i p f g hcart.w) := sorry

/-- The canonical derived base-change isomorphism for a cartesian square of slice sites. -/
@[stacks 0EZ0 "derived base-change isomorphism for a cartesian slice square"]
noncomputable def iso (hcart : IsPullback i p f g) :
    Over.pushforward J f ⋙ Over.pullback J g ≅
      Over.pullback J i ⋙ Over.pushforward J p :=
  @asIso _ _ _ _ (map J i p f g hcart.w) (map_isIso J i p f g hcart)

/-- The objectwise derived base-change isomorphism for a cartesian square of slice sites. -/
@[stacks 0EZ0 "objectwise derived base-change isomorphism"]
noncomputable def appIso (hcart : IsPullback i p f g)
    (K : DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max u v})) :
    (Over.pullback J g).obj ((Over.pushforward J f).obj K) ≅
      (Over.pushforward J p).obj ((Over.pullback J i).obj K) :=
  (iso J i p f g hcart).app K

/-- The forward map of the objectwise base-change isomorphism is the canonical base-change
component. -/
@[stacks 0EZ0 "objectwise derived base-change compatibility"]
theorem appIso_hom (hcart : IsPullback i p f g)
    (K : DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max u v})) :
    (appIso J i p f g hcart K).hom = app J i p f g hcart.w K := sorry

end CategoryTheory.GrothendieckTopology.Derived.Over.BaseChange

end
