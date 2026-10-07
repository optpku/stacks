module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Comma.Over.Map

/-!
# Absolute glueing of sheaves

This module owns the reusable slice-site descent datum underlying Stacks
Project Lemma 7.26.6.  It keeps concrete local sheaves, transition
isomorphisms, their category, and the two comparison functors in one acyclic
ReasLib leaf.  Coherence and descent proofs are intentionally deferred.
-/

@[expose] public section

open Opposite

universe u v w

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- An absolute glueing consists of sheaves on slice sites with coherent pullback transitions. -/
@[stacks 0GWK]
structure AbsoluteGlueing where
  /-- The local sheaf on the slice site over `U`. -/
  obj (U : C) : Sheaf (J.over U) (Type w)
  /-- Pullback along `f` identifies the local sheaf over `U` with that over `V`. -/
  transition {U V : C} (f : V ⟶ U) :
      (J.overMapPullback (Type w) f).obj (obj U) ≅ obj V
  /-- The identity transition agrees with the canonical pullback identity comparison. -/
  transition_id (U : C) :
      transition (𝟙 U) = (J.overMapPullbackId (Type w) U).app (obj U)
  /-- The transitions satisfy the pullback-composition cocycle. -/
  transition_comp {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
      (J.overMapPullbackComp (Type w) g f).app (obj U) ≪≫ transition (g ≫ f) =
        (J.overMapPullback (Type w) g).mapIso (transition f) ≪≫ transition g

namespace AbsoluteGlueing

/-- A morphism of absolute glueings is a local morphism family compatible with transitions. -/
@[stacks 0GWK, ext] structure Hom (F G : AbsoluteGlueing J) where
  /-- The local morphism over `U`. -/
  app (U : C) : F.obj U ⟶ G.obj U
  /-- Compatibility with pullback transitions. -/
  naturality {U V : C} (f : V ⟶ U) :
      CommSq ((J.overMapPullback (Type w) f).map (app U))
        (F.transition f).hom (G.transition f).hom (app V)

namespace Hom

/-- The identity local family is compatible with absolute-glueing transitions. -/
theorem idNaturality (F : AbsoluteGlueing J) {U V : C} (f : V ⟶ U) :
    CommSq ((J.overMapPullback (Type w) f).map (𝟙 (F.obj U)))
      (F.transition f).hom (F.transition f).hom (𝟙 (F.obj V)) := sorry

/-- The identity local morphism of an absolute glueing. -/
def id (F : AbsoluteGlueing J) :
    AbsoluteGlueing.Hom J F F where
  app U := 𝟙 (F.obj U)
  naturality := idNaturality J F

/-- Composite local families are compatible with absolute-glueing transitions. -/
theorem compNaturality {F G H : AbsoluteGlueing J}
    (α : AbsoluteGlueing.Hom J F G) (β : AbsoluteGlueing.Hom J G H) {U V : C} (f : V ⟶ U) :
    CommSq ((J.overMapPullback (Type w) f).map (α.app U ≫ β.app U))
      (F.transition f).hom (H.transition f).hom (α.app V ≫ β.app V) := sorry

/-- Composition of local morphisms of absolute glueings. -/
def comp {F G H : AbsoluteGlueing J} (α : AbsoluteGlueing.Hom J F G)
    (β : AbsoluteGlueing.Hom J G H) : AbsoluteGlueing.Hom J F H where
  app U := α.app U ≫ β.app U
  naturality := compNaturality J α β

/-- Left identity for absolute-glueing morphism composition. -/
theorem id_comp {F G : AbsoluteGlueing J} (α : AbsoluteGlueing.Hom J F G) :
    comp J (id J F) α = α := sorry

/-- Right identity for absolute-glueing morphism composition. -/
theorem comp_id {F G : AbsoluteGlueing J} (α : AbsoluteGlueing.Hom J F G) :
    comp J α (id J G) = α := sorry

/-- Associativity for absolute-glueing morphism composition. -/
theorem assoc {F G H K : AbsoluteGlueing J}
    (α : AbsoluteGlueing.Hom J F G) (β : AbsoluteGlueing.Hom J G H)
    (γ : AbsoluteGlueing.Hom J H K) :
    comp J (comp J α β) γ = comp J α (comp J β γ) := sorry

end Hom
end AbsoluteGlueing

/-- Absolute glueings and compatible local morphism families form a category. -/
instance : Category (AbsoluteGlueing J) where
  Hom F G := AbsoluteGlueing.Hom J F G
  id := AbsoluteGlueing.Hom.id J
  comp α β := AbsoluteGlueing.Hom.comp J α β
  id_comp := AbsoluteGlueing.Hom.id_comp J
  comp_id := AbsoluteGlueing.Hom.comp_id J
  assoc := AbsoluteGlueing.Hom.assoc J

namespace AbsoluteGlueing.FromSheaf

/-- The canonical slice transition of a sheaf agrees with pullback along an identity. -/
theorem transitionId (F : Sheaf J (Type w)) (U : C) :
    (Functor.sheafPushforwardContinuousComp' (Over.mapForget (𝟙 U))
      (Type w) (J.over U) (J.over U) J).app F =
      (J.overMapPullbackId (Type w) U).app (F.over U) := sorry

/-- The canonical slice transitions of a sheaf satisfy the pullback cocycle. -/
theorem transitionComp (F : Sheaf J (Type w)) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V) :
    (J.overMapPullbackComp (Type w) g f).app (F.over U) ≪≫
        (Functor.sheafPushforwardContinuousComp' (Over.mapForget (g ≫ f))
          (Type w) (J.over W) (J.over U) J).app F =
      (J.overMapPullback (Type w) g).mapIso
          ((Functor.sheafPushforwardContinuousComp' (Over.mapForget f)
            (Type w) (J.over V) (J.over U) J).app F) ≪≫
        (Functor.sheafPushforwardContinuousComp' (Over.mapForget g)
          (Type w) (J.over W) (J.over V) J).app F := sorry

/-- The canonical absolute glueing associated to a sheaf. -/
noncomputable def obj (F : Sheaf J (Type w)) : AbsoluteGlueing J where
  obj U := F.over U
  transition f :=
    (Functor.sheafPushforwardContinuousComp' (Over.mapForget f)
      (Type w) (J.over _) (J.over _) J).app F
  transition_id U := transitionId J F U
  transition_comp f g := transitionComp J F f g

/-- A sheaf morphism gives a compatible family of maps on its canonical slice glueings. -/
theorem mapNaturality {F G : Sheaf J (Type w)} (η : F ⟶ G)
    {U V : C} (f : V ⟶ U) :
    CommSq ((J.overMapPullback (Type w) f).map ((J.overPullback (Type w) U).map η))
      ((obj J F).transition f).hom
      ((obj J G).transition f).hom
      ((J.overPullback (Type w) V).map η) := sorry

/-- The morphism of canonical absolute glueings induced by a sheaf morphism. -/
noncomputable def map {F G : Sheaf J (Type w)} (η : F ⟶ G) :
    AbsoluteGlueing.Hom J (obj J F) (obj J G) where
  app U := (J.overPullback (Type w) U).map η
  naturality f := mapNaturality J η f

/-- Canonical absolute glueing preserves identity morphisms. -/
theorem map_id (F : Sheaf J (Type w)) :
    map J (𝟙 F) = 𝟙 (obj J F) := sorry

/-- Canonical absolute glueing preserves composition of sheaf morphisms. -/
theorem map_comp {F G H : Sheaf J (Type w)} (η : F ⟶ G) (θ : G ⟶ H) :
    map J (η ≫ θ) = AbsoluteGlueing.Hom.comp J (map J η) (map J θ) := sorry

/-- The restriction of a sheaf to all slice sites, equipped with its canonical transitions. -/
@[stacks 0GWK]
noncomputable def functor :
    Sheaf J (Type w) ⥤ AbsoluteGlueing J where
  obj := obj J
  map := map J
  map_id := map_id J
  map_comp := map_comp J

end AbsoluteGlueing.FromSheaf

namespace AbsoluteGlueing.ToSheaf.Presheaf

/-- Evaluating a transition at the terminal slice object gives the reconstructed local map. -/
noncomputable def transitionAppTerminal (F : AbsoluteGlueing J) {U V : C}
    (f : V ⟶ U) :
    (F.obj U).1.obj (Opposite.op (Over.mk f)) ⟶
      (F.obj V).1.obj (Opposite.op (Over.mk (𝟙 V))) :=
  (F.obj U).1.map (Over.mapIdentityIso f).hom.op ≫
    (F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V)))

/-- The reconstructed restriction map associated to `f : V ⟶ U`. -/
noncomputable def map (F : AbsoluteGlueing J) {U V : C} (f : V ⟶ U) :
    (F.obj U).1.obj (Opposite.op (Over.mk (𝟙 U))) ⟶
      (F.obj V).1.obj (Opposite.op (Over.mk (𝟙 V))) :=
  (F.obj U).1.map (Over.homMkTerminal f).op ≫
    transitionAppTerminal J F f

/-- The reconstructed restriction map is the identity along an identity arrow. -/
theorem map_id (F : AbsoluteGlueing J) (U : C) : map J F (𝟙 U) = 𝟙 _ := sorry

/-- The reconstructed restriction maps respect composition. -/
theorem map_comp (F : AbsoluteGlueing J) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V) :
    map J F (g ≫ f) = map J F f ≫ map J F g := sorry

/-- The presheaf reconstructed from terminal sections of an absolute glueing. -/
@[stacks 0GWK]
noncomputable def obj (F : AbsoluteGlueing J) : Cᵒᵖ ⥤ Type w where
  obj U := (F.obj U.unop).1.obj (Opposite.op (Over.mk (𝟙 U.unop)))
  map f := map J F f.unop
  map_id := sorry
  map_comp := sorry

end AbsoluteGlueing.ToSheaf.Presheaf

namespace AbsoluteGlueing.ToSheaf.OverIso

/-- The forward local comparison from a slice sheaf to the restriction of its reconstruction. -/
noncomputable def homApp (F : AbsoluteGlueing J) {U : C} (Y : Over U) :
    (F.obj U).1.obj (Opposite.op Y) ⟶
      (F.obj Y.left).1.obj (Opposite.op (Over.mk (𝟙 Y.left))) :=
  (F.obj U).1.map (Over.mkHomIso Y).hom.op ≫
    Presheaf.transitionAppTerminal J F Y.hom

/-- The inverse local comparison from reconstructed restricted sections to the original slice sheaf. -/
noncomputable def invApp (F : AbsoluteGlueing J) {U : C} (Y : Over U) :
    (F.obj Y.left).1.obj (Opposite.op (Over.mk (𝟙 Y.left))) ⟶
      (F.obj U).1.obj (Opposite.op Y) :=
  (F.transition Y.hom).inv.hom.app (Opposite.op (Over.mk (𝟙 Y.left))) ≫
    (F.obj U).1.map (Over.mapIdentityIso Y.hom).inv.op ≫
      (F.obj U).1.map (Over.mkHomIso Y).inv.op

/-- The forward and inverse local comparison maps compose to the identity on local sections. -/
theorem hom_inv_id (F : AbsoluteGlueing J) {U : C} (Y : Over U) :
    homApp J F Y ≫ invApp J F Y = 𝟙 _ := sorry

/-- The inverse and forward local comparison maps compose to the identity on reconstructed sections. -/
theorem inv_hom_id (F : AbsoluteGlueing J) {U : C} (Y : Over U) :
    invApp J F Y ≫ homApp J F Y = 𝟙 _ := sorry

/-- The forward local comparison maps are natural in slice morphisms. -/
theorem homNaturality (F : AbsoluteGlueing J) {U : C}
    {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    (F.obj U).1.map f ≫ homApp J F Y.unop =
      homApp J F X.unop ≫ ((Over.forget U).op ⋙ Presheaf.obj J F).map f := sorry

/-- The local sheaf over `U` is canonically isomorphic to the restriction of the reconstruction. -/
@[stacks 0GWK]
noncomputable def presheaf (F : AbsoluteGlueing J) (U : C) :
    (F.obj U).1 ≅ (Over.forget U).op ⋙ Presheaf.obj J F :=
  NatIso.ofComponents
    (fun X ↦
      { hom := homApp J F X.unop
        inv := invApp J F X.unop
        hom_inv_id := hom_inv_id J F X.unop
        inv_hom_id := inv_hom_id J F X.unop })
    (fun f ↦ homNaturality J F f)

end AbsoluteGlueing.ToSheaf.OverIso

namespace AbsoluteGlueing.ToSheaf.Presheaf

/-- The presheaf reconstructed from an absolute glueing satisfies the sheaf condition. -/
theorem isSheaf (F : AbsoluteGlueing J) :
    CategoryTheory.Presheaf.IsSheaf J (obj J F) := sorry

end AbsoluteGlueing.ToSheaf.Presheaf

namespace AbsoluteGlueing.ToSheaf

/-- The sheaf reconstructed from terminal sections of an absolute glueing. -/
@[stacks 0GWK]
noncomputable def obj (F : AbsoluteGlueing J) : Sheaf J (Type w) :=
  ⟨Presheaf.obj J F, Presheaf.isSheaf J F⟩

/-- The local sheaf of an absolute glueing is the corresponding slice of its reconstruction. -/
@[stacks 0GWK]
noncomputable def OverIso.sheaf (F : AbsoluteGlueing J) (U : C) :
    F.obj U ≅ ((FromSheaf.functor J).obj (obj J F)).obj U :=
  ObjectProperty.isoMk (CategoryTheory.Presheaf.IsSheaf (J.over U)) (OverIso.presheaf J F U)

namespace Presheaf.Hom

/-- Terminal evaluation of an absolute-glueing morphism on the reconstructed presheaves. -/
noncomputable def app {F G : AbsoluteGlueing J}
    (α : F ⟶ G) (U : Cᵒᵖ) :
    (Presheaf.obj J F).obj U ⟶ (Presheaf.obj J G).obj U :=
  (α.app U.unop).hom.app (Opposite.op (Over.mk (𝟙 U.unop)))

/-- Terminal evaluation of an absolute-glueing morphism respects reconstructed restrictions. -/
theorem naturality {F G : AbsoluteGlueing J} (α : F ⟶ G)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (Presheaf.obj J F).map f ≫ app J α V = app J α U ≫ (Presheaf.obj J G).map f := sorry

/-- The reconstructed presheaf morphism induced by an absolute-glueing morphism. -/
noncomputable def mk {F G : AbsoluteGlueing J} (α : F ⟶ G) :
    Presheaf.obj J F ⟶ Presheaf.obj J G where
  app := app J α
  naturality {_ _} f := naturality J α f

end Presheaf.Hom

/-- The sheaf morphism reconstructed from an absolute-glueing morphism. -/
noncomputable def map {F G : AbsoluteGlueing J} (α : F ⟶ G) : obj J F ⟶ obj J G :=
  ObjectProperty.homMk (Presheaf.Hom.mk J α)

/-- Reconstruction preserves identity morphisms. -/
theorem map_id (F : AbsoluteGlueing J) : map J (𝟙 F) = 𝟙 (obj J F) := sorry

/-- Reconstruction preserves composition of absolute-glueing morphisms. -/
theorem map_comp {F G H : AbsoluteGlueing J} (α : F ⟶ G) (β : G ⟶ H) :
    map J (α ≫ β) = map J α ≫ map J β := sorry

/-- Reconstruction of sheaves extends functorially to absolute glueing morphisms. -/
@[stacks 0GWK]
noncomputable def functor :
    AbsoluteGlueing J ⥤ Sheaf J (Type w) where
  obj := obj J
  map := map J
  map_id := map_id J
  map_comp := map_comp J

end AbsoluteGlueing.ToSheaf

namespace AbsoluteGlueing.Reconstruction.Unit

/-- Reconstructing a canonical absolute glueing recovers the original restriction map. -/
theorem presheafMap (F : Sheaf J (Type w)) {U V : C}
    (f : V ⟶ U) :
    ToSheaf.Presheaf.map J (FromSheaf.obj J F) f = F.obj.map f.op := sorry

/-- Naturality of the identity-component comparison for sheaf reconstruction. -/
theorem presheafNaturality (F : Sheaf J (Type w))
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    F.obj.map f ≫ (Iso.refl _).hom =
      (Iso.refl _).hom ≫ (ToSheaf.Presheaf.obj J (FromSheaf.obj J F)).map f := sorry

/-- Reconstructing the canonical absolute glueing of a sheaf gives the original presheaf. -/
noncomputable def presheafIso (F : Sheaf J (Type w)) :
    F.obj ≅ ToSheaf.Presheaf.obj J (FromSheaf.obj J F) :=
  NatIso.ofComponents
    (fun _ ↦ Iso.refl _)
    (fun f ↦ presheafNaturality J F f)

/-- The component of the reconstruction unit at a sheaf. -/
noncomputable def app (F : Sheaf J (Type w)) :
    F ≅ ((FromSheaf.functor J ⋙ ToSheaf.functor J).obj F) :=
  ObjectProperty.isoMk (CategoryTheory.Presheaf.IsSheaf J) (presheafIso J F)

/-- The reconstruction-unit components are natural in sheaf morphisms. -/
theorem naturality {F G : Sheaf J (Type w)}
    (η : F ⟶ G) :
    η ≫ (app J G).hom =
      (app J F).hom ≫ (FromSheaf.functor J ⋙ ToSheaf.functor J).map η := sorry

/-- The unit for the explicit absolute-glueing reconstruction. -/
@[stacks 0GWK]
noncomputable def iso :
    𝟭 (Sheaf J (Type w)) ≅ FromSheaf.functor J ⋙ ToSheaf.functor J :=
  NatIso.ofComponents (app J) (fun η ↦ naturality J η)

end AbsoluteGlueing.Reconstruction.Unit

namespace AbsoluteGlueing.Reconstruction.Counit

/-- The forward local comparison is compatible with absolute-glueing transitions. -/
theorem transitionCompat (F : AbsoluteGlueing J) {U V : C}
    (f : V ⟶ U) :
    CommSq ((J.overMapPullback (Type w) f).map (ToSheaf.OverIso.sheaf J F U).hom)
      (F.transition f).hom
      (((FromSheaf.functor J).obj (ToSheaf.obj J F)).transition f).hom
      (ToSheaf.OverIso.sheaf J F V).hom := sorry

/-- The inverse local comparison is compatible with absolute-glueing transitions. -/
theorem symmTransitionCompat (F : AbsoluteGlueing J) {U V : C}
    (f : V ⟶ U) :
    CommSq ((J.overMapPullback (Type w) f).map (ToSheaf.OverIso.sheaf J F U).symm.hom)
      (((FromSheaf.functor J).obj (ToSheaf.obj J F)).transition f).hom
      (F.transition f).hom
      (ToSheaf.OverIso.sheaf J F V).symm.hom := sorry

/-- The counit map from the canonical glueing of a reconstruction to the original datum. -/
noncomputable def hom (F : AbsoluteGlueing J) :
    AbsoluteGlueing.Hom J ((FromSheaf.functor J).obj (ToSheaf.obj J F)) F where
  app U := (ToSheaf.OverIso.sheaf J F U).symm.hom
  naturality f := symmTransitionCompat J F f

/-- The inverse counit map from an absolute glueing to the canonical glueing of its reconstruction. -/
noncomputable def inv (F : AbsoluteGlueing J) :
    AbsoluteGlueing.Hom J F ((FromSheaf.functor J).obj (ToSheaf.obj J F)) where
  app U := (ToSheaf.OverIso.sheaf J F U).hom
  naturality f := transitionCompat J F f

/-- The counit maps compose to the identity on the canonical glueing of a reconstruction. -/
theorem hom_inv_id (F : AbsoluteGlueing J) :
    AbsoluteGlueing.Hom.comp J (hom J F) (inv J F) =
      AbsoluteGlueing.Hom.id J ((FromSheaf.functor J).obj (ToSheaf.obj J F)) := sorry

/-- The counit maps compose to the identity on the original absolute glueing. -/
theorem inv_hom_id (F : AbsoluteGlueing J) :
    AbsoluteGlueing.Hom.comp J (inv J F) (hom J F) = AbsoluteGlueing.Hom.id J F := sorry

/-- The objectwise counit isomorphism for absolute-glueing reconstruction. -/
noncomputable def app (F : AbsoluteGlueing J) :
    ((ToSheaf.functor J ⋙ FromSheaf.functor J).obj F) ≅ F where
  hom := hom J F
  inv := inv J F
  hom_inv_id := hom_inv_id J F
  inv_hom_id := inv_hom_id J F

/-- The counit components are natural in absolute-glueing morphisms. -/
theorem naturality {F G : AbsoluteGlueing J} (α : F ⟶ G) :
    (ToSheaf.functor J ⋙ FromSheaf.functor J).map α ≫ (app J G).hom =
      (app J F).hom ≫ α := sorry

/-- The counit for the explicit absolute-glueing reconstruction. -/
@[stacks 0GWK]
noncomputable def iso :
    ToSheaf.functor J ⋙ FromSheaf.functor J ≅ 𝟭 (AbsoluteGlueing J) :=
  NatIso.ofComponents (app J) (fun α ↦ naturality J α)

end AbsoluteGlueing.Reconstruction.Counit

namespace AbsoluteGlueing

/-- Stacks Project Lemma 7.26.6 (0GWK): canonical restriction to slices is an equivalence. -/
@[stacks 0GWK]
noncomputable def sheafEquivalence :
    Sheaf J (Type w) ≌ AbsoluteGlueing J :=
  Equivalence.mk (FromSheaf.functor J) (ToSheaf.functor J)
    (Reconstruction.Unit.iso J) (Reconstruction.Counit.iso J)

namespace FromSheaf

/-- The explicit absolute-glueing equivalence supplies typeclass-based equivalence access. -/
@[stacks 0GWK]
instance functorIsEquivalence : Functor.IsEquivalence (functor J) :=
  Equivalence.isEquivalence_functor (sheafEquivalence J)

end FromSheaf
end AbsoluteGlueing

end CategoryTheory.GrothendieckTopology
