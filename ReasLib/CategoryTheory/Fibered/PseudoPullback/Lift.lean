module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism

/-! # Componentwise lifts into based pseudo-pullbacks

A supplied square of based functors determines its literal lift. The common base,
the two object and arrow images, and the comparison isomorphism are retained.
No universal-property existence certificate is used to select a functor.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor Bicategory

noncomputable section

universe u v uA vA uX vX uY vY uS vS

namespace CategoryTheory.BasedCategory.PseudoPullback

variable {C : Type u} [Category.{v} C]
variable {A : BasedCategory.{vA, uA} C}
variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}
variable (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
variable (left : A ⥤ᵇ X) (right : A ⥤ᵇ Y) (e : left ⋙ F ≅ right ⋙ G)

/-- The object of a supplied square over its original common base object. -/
def liftObj (a : A.obj) : (PseudoPullback F G).obj :=
  mk F G (A.p.obj a)
    { fst := ⟨left.obj a, left.w_obj a⟩
      snd := ⟨right.obj a, right.w_obj a⟩
      iso := Functor.Fiber.isoMk ((BasedNatIso.toNatIso e).app a) sorry }

/-- The arrow of a supplied square retains both specified component arrows. -/
def liftMap {a b : A.obj} (φ : a ⟶ b) :
    liftObj F G left right e a ⟶ liftObj F G left right e b :=
  Hom.mk (A.p.map φ) (left.map φ)
    (BasedFunctor.preserves_isHomLift left (A.p.map φ) φ)
    (right.map φ) (BasedFunctor.preserves_isHomLift right (A.p.map φ) φ) sorry

/-- Lift a supplied based square on its actual objects and morphisms. -/
def lift : A ⥤ᵇ PseudoPullback F G where
  toFunctor :=
    { obj := liftObj F G left right e
      map := liftMap F G left right e
      map_id := sorry
      map_comp := sorry }
  w := sorry

/-- The first projection of the literal lift has identity components. -/
def lift.fstIso : lift F G left right e ⋙ fst F G ≅ left :=
  BasedNatIso.ofComponents (fun _ => Iso.refl _) sorry sorry

/-- The second projection of the literal lift has identity components. -/
def lift.sndIso : lift F G left right e ⋙ snd F G ≅ right :=
  BasedNatIso.ofComponents (fun _ => Iso.refl _) sorry sorry

/-- The common base of the lifted object is the original base. -/
@[simp] theorem lift.obj_base (a : A.obj) :
    baseObj ((lift F G left right e).obj a) = A.p.obj a := rfl

/-- The first object projection is the supplied left object image. -/
@[simp] theorem lift.obj_fst (a : A.obj) :
    fstObj ((lift F G left right e).obj a) = left.obj a := rfl

/-- The second object projection is the supplied right object image. -/
@[simp] theorem lift.obj_snd (a : A.obj) :
    sndObj ((lift F G left right e).obj a) = right.obj a := rfl

/-- The comparison isomorphism is the supplied square component. -/
@[simp] theorem lift.obj_comparisonIso (a : A.obj) :
    comparisonIsoApp ((lift F G left right e).obj a) =
      (BasedNatIso.toNatIso e).app a := sorry

/-- The common base arrow is the original base arrow. -/
@[simp] theorem lift.map_base {a b : A.obj} (φ : a ⟶ b) :
    baseMap ((lift F G left right e).map φ) = A.p.map φ := rfl

/-- The first arrow projection is the supplied left arrow image. -/
@[simp] theorem lift.map_fst {a b : A.obj} (φ : a ⟶ b) :
    fstMap ((lift F G left right e).map φ) = left.map φ := rfl

/-- The second arrow projection is the supplied right arrow image. -/
@[simp] theorem lift.map_snd {a b : A.obj} (φ : a ⟶ b) :
    sndMap ((lift F G left right e).map φ) = right.map φ := rfl

end CategoryTheory.BasedCategory.PseudoPullback
