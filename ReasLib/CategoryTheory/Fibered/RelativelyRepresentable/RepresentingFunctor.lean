module

public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.TargetYoneda

/-!
# Representing functor of a relatively representable 1-morphism

A relatively representable 1-morphism `f : X ⟶ Y` of categories fibred in
groupoids has, for each object `y` of `Y`, a representing object of the
target-Hom functor `x ↦ ((toFunctor f).obj x ⟶ y)`. These representing
objects assemble uniquely into a functor `Y.total ⥤ X.total` right adjoint
to `toFunctor f`.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Functor Opposite
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids

variable {X Y : Groupoids C}

/-- The functor `u : Y.total ⥤ X.total` sending each object `y` of `Y` to a
chosen representing object of `targetYoneda f y`, and acting on morphisms by
the unique maps compatible with the canonical morphisms
`(toFunctor f).obj (u.obj y) ⟶ y`. -/
noncomputable def representingFunctor (f : X ⟶ Y)
    (h : targetYoneda.representable f) : Y.total ⥤ X.total :=
  (toFunctor f).rightAdjointObjIsDefined.lift (𝟭 _) (fun y ↦ h y) ⋙
    (toFunctor f).partialRightAdjoint

/-- On objects, `representingFunctor f h` is the chosen representing object of
`targetYoneda f y`. -/
theorem representingFunctor_obj (f : X ⟶ Y) (h : targetYoneda.representable f)
    (y : Y.total) :
    (representingFunctor f h).obj y = (targetYoneda f y).reprX (hF := h y) :=
  sorry

namespace representingFunctor

/-- The universal hom-equivalence `(x ⟶ u.obj y) ≃ ((toFunctor f).obj x ⟶ y)`
exhibiting `u.obj y` as representing `targetYoneda f y`. -/
noncomputable def homEquiv (f : X ⟶ Y) (h : targetYoneda.representable f)
    (x : X.total) (y : Y.total) :
    (x ⟶ (representingFunctor f h).obj y) ≃ ((toFunctor f).obj x ⟶ y) :=
  ((targetYoneda f y).representableBy (hF := h y)).homEquiv

/-- The adjunction `toFunctor f ⊣ representingFunctor f h` assembled from the
representing hom-equivalences. -/
noncomputable def adjunction (f : X ⟶ Y) (h : targetYoneda.representable f) :
    toFunctor f ⊣ representingFunctor f h :=
  Adjunction.adjunctionOfEquivRight
    (fun (x : X.total) (y : Y.total) ↦ (homEquiv f h x y).symm)
    (fun _ _ y α g ↦
      (((targetYoneda f y).representableBy (hF := h y)).comp_homEquiv_symm g α).symm)

/-- The chosen representing functor is right adjoint to the total functor. -/
instance isRightAdjoint (f : X ⟶ Y) (h : targetYoneda.representable f) :
    (representingFunctor f h).IsRightAdjoint :=
  (adjunction f h).isRightAdjoint

/-- The adjunction hom-equivalence is the opposite of `homEquiv`. -/
theorem adjunction_homEquiv (f : X ⟶ Y) (h : targetYoneda.representable f)
    (x : X.total) (y : Y.total) :
    (adjunction f h).homEquiv x y = (homEquiv f h x y).symm :=
  sorry

/-- The canonical morphism `(toFunctor f).obj (u.obj y) ⟶ y` associated with the
representing object `u.obj y`. -/
noncomputable def counit_app (f : X ⟶ Y) (h : targetYoneda.representable f)
    (y : Y.total) :
    (toFunctor f).obj ((representingFunctor f h).obj y) ⟶ y :=
  (homEquiv f h ((representingFunctor f h).obj y) y) (𝟙 _)

/-- `counit_app` is the counit of `representingFunctor.adjunction` at `y`. -/
theorem counit_app_eq (f : X ⟶ Y) (h : targetYoneda.representable f)
    (y : Y.total) :
    counit_app f h y = (adjunction f h).counit.app y :=
  sorry

/-- The structure morphism `p(u(y)) ⟶ q(y)` obtained by applying the target
projection to the counit `(toFunctor f).obj (u.obj y) ⟶ y`. -/
noncomputable def structureMap (f : X ⟶ Y) (h : targetYoneda.representable f)
    (y : Y.total) :
    X.p.obj ((representingFunctor f h).obj y) ⟶ Y.p.obj y :=
  eqToHom
      ((congrArg (fun G ↦ G.obj ((representingFunctor f h).obj y)) (comm f)).symm) ≫
    Y.p.map (counit_app f h y)

/-- The canonical comparison of the right Kan extension along `(toFunctor f).op`
at `y` with the value of a presheaf at the representing object `u(y)`. -/
noncomputable def pushforwardComparison (f : X ⟶ Y)
    (h : targetYoneda.representable f)
    [∀ P : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor f).op P]
    (F : X.totalᵒᵖ ⥤ Type w) (y : Y.total) :
    ((toFunctor f).op.ran.obj F).obj (op y) ⟶
      F.obj (op ((representingFunctor f h).obj y)) :=
  ((toFunctor f).op.ran.obj F).map (op (counit_app f h y)) ≫
    ((toFunctor f).op.ranCounit.app F).app (op ((representingFunctor f h).obj y))

end representingFunctor

end FiberedCategoryOver.Groupoids

end CategoryTheory
