module

public import ReasLib.CategoryTheory.Functor.PresheafFiber

/-!
# Maps between presheaf fibers

A natural transformation between set-valued functors induces a natural map
between their presheaf fiber functors.  This is the functoriality of the
colimit presentation used by `Functor.presheafFiber`.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v w

noncomputable section

namespace CategoryTheory.NatTrans

variable {C : Type u} [Category.{v} C]
variable {p q : C ⥤ Type w}
variable [HasColimitsOfShape p.Elementsᵒᵖ (Type w)]
variable [HasColimitsOfShape q.Elementsᵒᵖ (Type w)]

/-- The generator maps defined by `η : p ⟶ q` satisfy the compatibility relation required to
descend from the presheaf fiber of `p`. -/
theorem presheafFiberApp_compatible (η : p ⟶ q) (F : Cᵒᵖ ⥤ Type w) :
    ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : p.obj X),
      F.map f.op ≫ q.toPresheafFiber X (η.app X x) F =
        q.toPresheafFiber Y (η.app Y (p.map f x)) F := sorry

/-- The map on the fiber of a presheaf induced by a natural transformation of set-valued
functors. -/
noncomputable def presheafFiberApp (η : p ⟶ q) (F : Cᵒᵖ ⥤ Type w) :
    p.presheafFiber.obj F ⟶ q.presheafFiber.obj F :=
  p.presheafFiberDesc
    (fun X x ↦ q.toPresheafFiber X (η.app X x) F)
    (η.presheafFiberApp_compatible F)

/-- The induced fiber map sends a canonical generator to the generator indexed by its image
under `η`. -/
@[simp, reassoc]
theorem toPresheafFiber_presheafFiberApp (η : p ⟶ q) (F : Cᵒᵖ ⥤ Type w)
    (X : C) (x : p.obj X) :
    p.toPresheafFiber X x F ≫ η.presheafFiberApp F =
      q.toPresheafFiber X (η.app X x) F := sorry

/-- The fiber maps induced by `η` are natural in the presheaf argument. -/
theorem presheafFiberApp_naturality (η : p ⟶ q) {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) :
    p.presheafFiber.map f ≫ η.presheafFiberApp G =
      η.presheafFiberApp F ≫ q.presheafFiber.map f := sorry

/-- The natural transformation of presheaf fiber functors induced by `η`. -/
noncomputable def presheafFiber (η : p ⟶ q) :
    p.presheafFiber ⟶ q.presheafFiber where
  app := η.presheafFiberApp
  naturality _ _ f := η.presheafFiberApp_naturality f

/-- Evaluating `η.presheafFiber` on a canonical generator has the expected pointwise formula. -/
@[simp, reassoc]
theorem toPresheafFiber_presheafFiber_app (η : p ⟶ q) (F : Cᵒᵖ ⥤ Type w)
    (X : C) (x : p.obj X) :
    p.toPresheafFiber X x F ≫ (η.presheafFiber).app F =
      q.toPresheafFiber X (η.app X x) F := sorry

/-- Taking presheaf fibers sends the identity natural transformation to the identity map. -/
@[simp]
theorem presheafFiber_id (p : C ⥤ Type w)
    [HasColimitsOfShape p.Elementsᵒᵖ (Type w)] :
    presheafFiber (𝟙 p : p ⟶ p) = 𝟙 p.presheafFiber := sorry

/-- Taking presheaf fibers preserves composition of natural transformations. -/
@[simp]
theorem presheafFiber_comp {r : C ⥤ Type w}
    [HasColimitsOfShape r.Elementsᵒᵖ (Type w)]
    (η : p ⟶ q) (θ : q ⟶ r) :
    (η ≫ θ).presheafFiber = η.presheafFiber ≫ θ.presheafFiber := sorry

end CategoryTheory.NatTrans
