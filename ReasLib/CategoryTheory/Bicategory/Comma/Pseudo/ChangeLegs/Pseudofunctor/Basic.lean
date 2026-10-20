module

public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.ChangeLegs.Pseudofunctor.Identity
public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.ChangeLegs.Pseudofunctor.Composition

/-!
# The pseudofunctor changing pseudo comma legs

This leaf assembles the explicit change-of-legs action and its identity and
composition comparisons into a pseudofunctor. The private statements below
supply only functoriality and bicategorical coherence fields.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe wA vA uA wB vB uB wC vC uC

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

namespace PseudoComma

variable {F F' : A ⥤ᵖ C} {G G' : B ⥤ᵖ C}

namespace Implementation

/-- Changing pseudo comma legs preserves identity `2`-morphisms. -/
private theorem map₂_id
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T : PseudoComma F G} (u : S ⟶ T) :
    changeLegs.map₂ α β (𝟙 u) =
      𝟙 (changeLegs.map α β u) := sorry

/-- Changing pseudo comma legs preserves vertical composition of
`2`-morphisms. -/
private theorem map₂_comp
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T : PseudoComma F G} {u v w : S ⟶ T}
    (η : u ⟶ v) (θ : v ⟶ w) :
    changeLegs.map₂ α β (η ≫ θ) =
      changeLegs.map₂ α β η ≫ changeLegs.map₂ α β θ := sorry

/-- The explicit prelax core of changing two pseudo comma legs. -/
private noncomputable def prelax
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G') :
    PrelaxFunctor (PseudoComma F G) (PseudoComma F' G') where
  obj := changeLegs.obj α β
  map := changeLegs.map α β
  map₂ := changeLegs.map₂ α β
  map₂_id := map₂_id α β
  map₂_comp := map₂_comp α β

/-- Changing pseudo comma legs preserves left whiskering up to its explicit
composition comparisons. -/
private theorem map₂_whiskerLeft
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G') :
    ∀ {S T U : PseudoComma F G} (u : S ⟶ T)
      {v w : T ⟶ U} (η : v ⟶ w),
      (prelax α β).map₂ (u ◁ η) =
        (changeLegs.mapComp α β u v).hom ≫
          (prelax α β).map u ◁ (prelax α β).map₂ η ≫
          (changeLegs.mapComp α β u w).inv := sorry

/-- Changing pseudo comma legs preserves right whiskering up to its explicit
composition comparisons. -/
private theorem map₂_whiskerRight
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G') :
    ∀ {S T U : PseudoComma F G}
      {u v : S ⟶ T} (η : u ⟶ v) (w : T ⟶ U),
      (prelax α β).map₂ (η ▷ w) =
        (changeLegs.mapComp α β u w).hom ≫
          (prelax α β).map₂ η ▷ (prelax α β).map w ≫
          (changeLegs.mapComp α β v w).inv := sorry

/-- Changing pseudo comma legs preserves associators. -/
private theorem map₂_associator
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G') :
    ∀ {R S T U : PseudoComma F G}
      (u : R ⟶ S) (v : S ⟶ T) (w : T ⟶ U),
      (prelax α β).map₂ (α_ u v w).hom =
        (changeLegs.mapComp α β (u ≫ v) w).hom ≫
          (changeLegs.mapComp α β u v).hom ▷ (prelax α β).map w ≫
          (α_ ((prelax α β).map u) ((prelax α β).map v)
            ((prelax α β).map w)).hom ≫
          (prelax α β).map u ◁ (changeLegs.mapComp α β v w).inv ≫
          (changeLegs.mapComp α β u (v ≫ w)).inv := sorry

/-- Changing pseudo comma legs preserves left unitors. -/
private theorem map₂_leftUnitor
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G') :
    ∀ {S T : PseudoComma F G} (u : S ⟶ T),
      (prelax α β).map₂ (λ_ u).hom =
        (changeLegs.mapComp α β (𝟙 S) u).hom ≫
          (changeLegs.mapId α β S).hom ▷ (prelax α β).map u ≫
          (λ_ ((prelax α β).map u)).hom := sorry

/-- Changing pseudo comma legs preserves right unitors. -/
private theorem map₂_rightUnitor
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G') :
    ∀ {S T : PseudoComma F G} (u : S ⟶ T),
      (prelax α β).map₂ (ρ_ u).hom =
        (changeLegs.mapComp α β u (𝟙 T)).hom ≫
          (prelax α β).map u ◁ (changeLegs.mapId α β T).hom ≫
          (ρ_ ((prelax α β).map u)).hom := sorry

end Implementation

/-- Change the two legs of a pseudo comma bicategory by a strong
transformation contravariantly on the left and covariantly on the right.

For `α : F' ⟶ F` and `β : G ⟶ G'`, this sends a structural map `S.hom` to
`α.app S.left ≫ S.hom ≫ β.app S.right`. Its identity and composition
comparisons are `changeLegs.mapId` and `changeLegs.mapComp`. -/
noncomputable def changeLegs
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G') :
    Pseudofunctor (PseudoComma F G) (PseudoComma F' G') where
  toPrelaxFunctor := Implementation.prelax α β
  mapId := changeLegs.mapId α β
  mapComp := changeLegs.mapComp α β
  map₂_whisker_left := Implementation.map₂_whiskerLeft α β
  map₂_whisker_right := Implementation.map₂_whiskerRight α β
  map₂_associator := Implementation.map₂_associator α β
  map₂_left_unitor := Implementation.map₂_leftUnitor α β
  map₂_right_unitor := Implementation.map₂_rightUnitor α β

/- Data and axiom audit (mathlib 4.32):

`changeLegs` retains the explicit object, morphism, and cell owners from
`ChangeLegs.Basic`; its private helpers supply only functoriality and
bicategorical coherence propositions. `#print axioms` also sees the inherited
`PseudoComma` multiplicativity proof debt; its non-`Prop` fields are the
explicit owners from the lower leaves. -/

end PseudoComma

end Bicategory

end CategoryTheory
