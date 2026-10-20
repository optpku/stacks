module

public import ReasLib.CategoryTheory.Pro.Presentation

@[expose] public section

open CategoryTheory Opposite
open scoped CategoryTheory

noncomputable section

universe uA vA uB vB uC vC

namespace CategoryTheory.Pro

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]

/-- The bifunctor of morphisms from a `Pro B`-valued functor to constant pro-objects. -/
noncomputable def representedHom (F : A ⥤ Pro B) : Aᵒᵖ × B ⥤ Type vB :=
  (F.op.prod (Pro.yoneda : B ⥤ Pro B)) ⋙ Functor.hom (Pro B)

/-- Objectwise, `representedHom F` is the Hom type from `F.obj K` to the constant
pro-object on `L`. -/
theorem representedHom_obj (F : A ⥤ Pro B) (K : A) (L : B) :
    (representedHom F).obj (op K, L) = (F.obj K ⟶ Pro.yoneda.obj L) := sorry

/-- The Yoneda realization of a pro-object, evaluated on a constant pro-object. -/
noncomputable def homYonedaEquiv (X : Pro B) (L : B) :
    (X ⟶ Pro.yoneda.obj L) ≃ ((Pro.inclusion B).obj X).unop.obj L :=
  (inclusion.fullyFaithful.homEquiv).trans <|
    (opEquiv _ _).trans <|
      (Iso.homCongr (Coyoneda.opIso.app (Opposite.op L)) (Iso.refl _)).trans coyonedaEquiv

/-- Applying the inverse Yoneda realization after the forward map recovers the
pro-morphism. -/
theorem homYonedaEquiv_symm_apply (X : Pro B) (L : B)
    (f : X ⟶ Pro.yoneda.obj L) :
    (homYonedaEquiv X L).symm (homYonedaEquiv X L f) = f := sorry

/-- Naturality of the objectwise identification between `representedHom` and the
uncurried Yoneda realization. -/
theorem representedHomRealizationIso_naturality (F : A ⥤ Pro B)
    {p q : Aᵒᵖ × B} (f : p ⟶ q) :
    (representedHom F).map f ≫
        (homYonedaEquiv (F.obj q.1.unop) q.2).toIso.hom =
      (homYonedaEquiv (F.obj p.1.unop) p.2).toIso.hom ≫
        (Functor.uncurry.obj (F ⋙ Pro.inclusion B).leftOp).map f := sorry

/-- The represented Hom bifunctor is canonically the uncurried fully faithful
realization of the corresponding pro-valued functor. -/
noncomputable def representedHomRealizationIso (F : A ⥤ Pro B) :
    representedHom F ≅ Functor.uncurry.obj (F ⋙ Pro.inclusion B).leftOp :=
  NatIso.ofComponents
    (fun p ↦ (homYonedaEquiv (F.obj p.1.unop) p.2).toIso)
    (fun f ↦ representedHomRealizationIso_naturality F f)

/-- The forward component of `representedHomRealizationIso` is `homYonedaEquiv`. -/
theorem representedHomRealizationIso_hom_app (F : A ⥤ Pro B) (p : Aᵒᵖ × B) :
    (representedHomRealizationIso F).hom.app p =
      (homYonedaEquiv (F.obj p.1.unop) p.2).toIso.hom := sorry

/-- Taking `leftOp` and then removing it recovers a transformation into an opposite
category. -/
theorem removeLeftOp_leftOp
    {F G : A ⥤ (B ⥤ Type vB)ᵒᵖ} (η : F ⟶ G) :
    NatTrans.removeLeftOp η.leftOp = η := sorry

/-- Removing `leftOp` and then taking it again recovers a transformation between
ordinary functor categories. -/
theorem leftOp_removeLeftOp
    {F G : A ⥤ (B ⥤ Type vB)ᵒᵖ} (η : G.leftOp ⟶ F.leftOp) :
    (NatTrans.removeLeftOp η).leftOp = η := sorry

/-- Morphisms of functors into an opposite category are equivalently reversed
transformations between their `leftOp` functors. -/
def leftOpHomEquiv (F G : A ⥤ (B ⥤ Type vB)ᵒᵖ) :
    (F ⟶ G) ≃ (G.leftOp ⟶ F.leftOp) where
  toFun := NatTrans.leftOp
  invFun := NatTrans.removeLeftOp
  left_inv := removeLeftOp_leftOp
  right_inv := leftOp_removeLeftOp

/-- The forward direction of `leftOpHomEquiv` is componentwise opposite. -/
theorem leftOpHomEquiv_apply (F G : A ⥤ (B ⥤ Type vB)ᵒᵖ) (η : F ⟶ G) :
    leftOpHomEquiv F G η = η.leftOp := sorry

/-- Natural transformations between pro-valued functors are equivalently reversed
natural transformations between their represented Hom bifunctors. -/
noncomputable def representedHomNatTransEquiv (F G : A ⥤ Pro B) :
    (F ⟶ G) ≃ (representedHom G ⟶ representedHom F) :=
  (inclusion.fullyFaithful.whiskeringRight A).homEquiv |>.trans
    (leftOpHomEquiv (F ⋙ Pro.inclusion B) (G ⋙ Pro.inclusion B)) |>.trans
      Functor.fullyFaithfulUncurry.homEquiv |>.trans
        (Iso.homCongr (representedHomRealizationIso G).symm
          (representedHomRealizationIso F).symm)

/-- Under `representedHomNatTransEquiv`, a transformation acts by precomposition on
each represented Hom type. -/
theorem representedHomNatTransEquiv_apply (F G : A ⥤ Pro B) (η : F ⟶ G)
    (K : A) (L : B) (b : G.obj K ⟶ Pro.yoneda.obj L) :
    (representedHomNatTransEquiv F G η).app (Opposite.op K, L) b =
      η.app K ≫ b := sorry

/-- The inverse represented-Hom construction recovers the original natural
transformation. -/
theorem representedHomNatTransEquiv_symm_apply (F G : A ⥤ Pro B)
    (η : F ⟶ G) :
    (representedHomNatTransEquiv F G).symm
      (representedHomNatTransEquiv F G η) = η := sorry

/-- An isomorphism of represented Hom bifunctors determines an isomorphism of the
underlying pro-valued functors: two `Pro B`-valued functors are naturally isomorphic when
their represented Hom bifunctors are. -/
noncomputable def representedHomIsoOf (F G : A ⥤ Pro B)
    (e : representedHom G ≅ representedHom F) : F ≅ G where
  hom := (representedHomNatTransEquiv F G).symm e.hom
  inv := (representedHomNatTransEquiv G F).symm e.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward transformation of `representedHomIsoOf` is the transformation corresponding
to `e.hom` under `representedHomNatTransEquiv`. -/
@[simp]
theorem representedHomIsoOf_hom (F G : A ⥤ Pro B)
    (e : representedHom G ≅ representedHom F) :
    (representedHomIsoOf F G e).hom = (representedHomNatTransEquiv F G).symm e.hom := rfl

/-- The inverse transformation of `representedHomIsoOf` is the transformation corresponding
to `e.inv` under `representedHomNatTransEquiv`. -/
@[simp]
theorem representedHomIsoOf_inv (F G : A ⥤ Pro B)
    (e : representedHom G ≅ representedHom F) :
    (representedHomIsoOf F G e).inv = (representedHomNatTransEquiv G F).symm e.inv := rfl

/-- Applying represented Hom to an isomorphism reverses its direction. -/
noncomputable def representedHomIsoMap (F G : A ⥤ Pro B) (e : F ≅ G) :
    representedHom G ≅ representedHom F where
  hom := representedHomNatTransEquiv F G e.hom
  inv := representedHomNatTransEquiv G F e.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Isomorphisms of pro-valued functors are equivalent to reversed isomorphisms of
their represented Hom bifunctors. -/
noncomputable def representedHomIsoEquiv (F G : A ⥤ Pro B) :
    (F ≅ G) ≃ (representedHom G ≅ representedHom F) where
  toFun := representedHomIsoMap F G
  invFun := representedHomIsoOf F G
  left_inv := sorry
  right_inv := sorry

/-- The inverse represented-Hom image has the prescribed forward transformation. -/
theorem representedHomIsoEquiv_symm_hom (F G : A ⥤ Pro B)
    (e : representedHom G ≅ representedHom F) :
    ((representedHomIsoEquiv F G).symm e).hom =
      (representedHomNatTransEquiv F G).symm e.hom := sorry

variable {C : Type uC} [Category.{vC} C]

/-- Naturality of the identity-component comparison for represented Hom after
precomposition. -/
theorem representedHomPrecompIso_naturality (H : A ⥤ B) (F : B ⥤ Pro C)
    {p q : Aᵒᵖ × C} (f : p ⟶ q) :
    (representedHom (H ⋙ F)).map f ≫ 𝟙 _ =
      𝟙 _ ≫ ((H.op.prod (𝟭 C)) ⋙ representedHom F).map f := sorry

/-- Represented Hom commutes canonically with precomposition of a pro-valued functor. -/
noncomputable def representedHomPrecompIso (H : A ⥤ B) (F : B ⥤ Pro C) :
    representedHom (H ⋙ F) ≅ (H.op.prod (𝟭 C)) ⋙ representedHom F :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun f ↦ representedHomPrecompIso_naturality H F f)

/-- Every component of `representedHomPrecompIso` is the identity map. -/
theorem representedHomPrecompIso_hom_app (H : A ⥤ B) (F : B ⥤ Pro C)
    (p : Aᵒᵖ × C) :
    (representedHomPrecompIso H F).hom.app p = 𝟙 _ := sorry


end CategoryTheory.Pro
