module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Definition

/-!
# Fiber action of cartesian based functor morphisms

This module packages the action of the hom-category of cartesian based functors on each standard
fiber.  It exposes the induced natural transformations and isomorphisms without requiring users
to pass manually through the full-subcategory morphism and `BasedNatTrans.fiber`.
-/

@[expose] public section

namespace CategoryTheory

universe u v uS₁ vS₁ uS₂ vS₂

variable {C : Type u} [Category.{v} C]

namespace CartesianBasedFunctor

variable {S₁ : Type uS₁} {S₂ : Type uS₂} [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}
variable {F G H : CartesianBasedFunctor p₁ p₂}

/-- Restrict a morphism of cartesian based functors to a natural transformation on the standard
fiber over `U`. -/
def fiberNatTrans (eta : F ⟶ G) (U : C) :
    F.fiberFunctor U ⟶ G.fiberFunctor U :=
  BasedNatTrans.fiber (toBasedNatTrans eta) U

/-- Evaluation of a restricted cartesian-functor morphism is the canonical bundled fiber
component of its underlying based natural transformation. -/
@[simp]
theorem fiberNatTrans.app (eta : F ⟶ G) (U : C) (x : p₁.Fiber U) :
    (fiberNatTrans eta U).app x =
      BasedNatTrans.fiberApp (toBasedNatTrans eta) U x := sorry

/-- Forgetting a restricted component to the total category recovers the corresponding
component of the underlying based natural transformation. -/
@[simp]
theorem fiberNatTrans.app.val (eta : F ⟶ G) (U : C) (x : p₁.Fiber U) :
    ((fiberNatTrans eta U).app x).1 =
      (toBasedNatTrans eta).toNatTrans.app x.1 := sorry

/-- Naturality of a cartesian-functor morphism after restriction to a standard fiber. -/
@[reassoc]
theorem fiberNatTrans.naturality (eta : F ⟶ G) (U : C)
    {x y : p₁.Fiber U} (phi : x ⟶ y) :
    (F.fiberFunctor U).map phi ≫ (fiberNatTrans eta U).app y =
      (fiberNatTrans eta U).app x ≫ (G.fiberFunctor U).map phi := sorry

/-- Restriction of cartesian-functor morphisms to a fiber preserves identities. -/
@[simp]
theorem fiberNatTrans.id (F : CartesianBasedFunctor p₁ p₂) (U : C) :
    fiberNatTrans (𝟙 F) U = 𝟙 (F.fiberFunctor U) := sorry

/-- Restriction of cartesian-functor morphisms to a fiber preserves vertical composition. -/
@[simp]
theorem fiberNatTrans.comp (eta : F ⟶ G) (theta : G ⟶ H) (U : C) :
    fiberNatTrans (eta ≫ theta) U =
      fiberNatTrans eta U ≫ fiberNatTrans theta U := sorry

/-- For fixed projections and a base object, evaluation on the standard fiber is a functor from
the hom-category of cartesian based functors to the ordinary functor category of fibers. -/
def fiberHomFunctor (p₁ : S₁ ⥤ C) (p₂ : S₂ ⥤ C) (U : C) :
    CartesianBasedFunctor p₁ p₂ ⥤ (p₁.Fiber U ⥤ p₂.Fiber U) where
  obj F := F.fiberFunctor U
  map eta := fiberNatTrans eta U
  map_id F := fiberNatTrans.id F U
  map_comp eta theta := fiberNatTrans.comp eta theta U

/-- The object action of `fiberHomFunctor` is the fiber functor induced by the cartesian based
functor. -/
@[simp]
theorem fiberHomFunctor.obj (F : CartesianBasedFunctor p₁ p₂) (U : C) :
    (fiberHomFunctor p₁ p₂ U).obj F = F.fiberFunctor U := sorry

/-- The morphism action of `fiberHomFunctor` is restriction of the underlying based natural
transformation. -/
@[simp]
theorem fiberHomFunctor.map (eta : F ⟶ G) (U : C) :
    (fiberHomFunctor p₁ p₂ U).map eta = fiberNatTrans eta U := sorry

/-- The component of the morphism action of `fiberHomFunctor` is the canonical bundled fiber
component. -/
@[simp]
theorem fiberHomFunctor.map.app (eta : F ⟶ G) (U : C) (x : p₁.Fiber U) :
    ((fiberHomFunctor p₁ p₂ U).map eta).app x =
      BasedNatTrans.fiberApp (toBasedNatTrans eta) U x := sorry

/-- Forgetting a component of the morphism action of `fiberHomFunctor` recovers the original
total-category component. -/
@[simp]
theorem fiberHomFunctor.map.app.val (eta : F ⟶ G) (U : C) (x : p₁.Fiber U) :
    (((fiberHomFunctor p₁ p₂ U).map eta).app x).1 =
      (toBasedNatTrans eta).toNatTrans.app x.1 := sorry

/-- Restrict an isomorphism of cartesian based functors to an isomorphism of their induced fiber
functors. -/
def fiberIso (e : F ≅ G) (U : C) : F.fiberFunctor U ≅ G.fiberFunctor U :=
  (fiberHomFunctor p₁ p₂ U).mapIso e

/-- The forward transformation of a restricted cartesian-functor isomorphism is the restriction
of its forward morphism. -/
@[simp]
theorem fiberIso.hom (e : F ≅ G) (U : C) :
    (fiberIso e U).hom = fiberNatTrans e.hom U := sorry

/-- The inverse transformation of a restricted cartesian-functor isomorphism is the restriction
of its inverse morphism. -/
@[simp]
theorem fiberIso.inv (e : F ≅ G) (U : C) :
    (fiberIso e U).inv = fiberNatTrans e.inv U := sorry

/-- The forward component of a restricted cartesian-functor isomorphism is the canonical bundled
fiber component of its forward morphism. -/
@[simp]
theorem fiberIso.hom.app (e : F ≅ G) (U : C) (x : p₁.Fiber U) :
    (fiberIso e U).hom.app x =
      BasedNatTrans.fiberApp (toBasedNatTrans e.hom) U x := sorry

/-- The inverse component of a restricted cartesian-functor isomorphism is the canonical bundled
fiber component of its inverse morphism. -/
@[simp]
theorem fiberIso.inv.app (e : F ≅ G) (U : C) (x : p₁.Fiber U) :
    (fiberIso e U).inv.app x =
      BasedNatTrans.fiberApp (toBasedNatTrans e.inv) U x := sorry

/-- Restricting the identity cartesian-functor isomorphism gives the identity fiber
isomorphism. -/
@[simp]
theorem fiberIso.refl (F : CartesianBasedFunctor p₁ p₂) (U : C) :
    fiberIso (Iso.refl F) U = Iso.refl (F.fiberFunctor U) := sorry

/-- Restriction of cartesian-functor isomorphisms to a fiber commutes with symmetry. -/
@[simp]
theorem fiberIso.symm (e : F ≅ G) (U : C) :
    fiberIso e.symm U = (fiberIso e U).symm := sorry

/-- Restriction of cartesian-functor isomorphisms to a fiber preserves composition. -/
theorem fiberIso.trans (e : F ≅ G) (d : G ≅ H) (U : C) :
    fiberIso (e ≪≫ d) U = fiberIso e U ≪≫ fiberIso d U := sorry

end CartesianBasedFunctor

end CategoryTheory

/- Axiom audit: `fiberNatTrans`, `fiberHomFunctor`, and `fiberIso` retain only the canonical
underlying based-natural-transformation data; any `sorryAx` is confined to their Prop-valued
computation and category-law fields. -/
