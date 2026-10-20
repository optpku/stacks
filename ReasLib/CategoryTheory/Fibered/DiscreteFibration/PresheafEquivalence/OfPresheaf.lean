module

public import ReasLib.CategoryTheory.Fibered.InSets.Bicategory
public import ReasLib.CategoryTheory.Fibered.InSets.Hom
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.FullSubbicategory
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Elements
import Mathlib.Tactic.CrossRefAttribute

/-!
# Discrete Grothendieck construction

This leaf contains the construction from a set-valued presheaf to a category
fibred in sets, together with its fiberwise computation API.
-/

@[expose] public section

universe w u v uS vS

namespace CategoryTheory

open Opposite
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Sets

section OfPresheafImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The opposite category-of-elements map commutes strictly with its projection to `C`.

Proof strategy: this is the opposite form of `CategoryOfElements.map_π` and is definitionally
reflexive on objects and morphisms. -/
private theorem mapOp_comp_leftOp_π
    {F G : Cᵒᵖ ⥤ Type w} (α : F ⟶ G) :
    (CategoryOfElements.map α).op ⋙ (CategoryOfElements.π G).leftOp =
      (CategoryOfElements.π F).leftOp := sorry

/-- The raw owner morphism induced by a presheaf map. It is used only to assemble
`ofPresheaf`; its underlying functor is exposed by `ofPresheaf.map.toFunctor`. -/
private def ofPresheafMap
    {F G : Cᵒᵖ ⥤ Type w} (α : F ⟶ G) :
    FiberedCategoryOver.Sets.ofFunctor ((CategoryOfElements.π F).leftOp) ⟶
      FiberedCategoryOver.Sets.ofFunctor ((CategoryOfElements.π G).leftOp) :=
  FiberedCategoryOver.Sets.ofBasedFunctor
    (BasedFunctor.ofFunctor (CategoryOfElements.map α).op (mapOp_comp_leftOp_π α))

/-- The raw category-of-elements map preserves identity morphisms.

Proof strategy: project to the underlying based functor and use
`CategoryOfElements.map_id_map`, equivalently extensionality on its definitional object and
morphism formulas. -/
private theorem ofPresheafMap_id
    (F : Cᵒᵖ ⥤ Type w) :
    ofPresheafMap (𝟙 F) =
      𝟙 (FiberedCategoryOver.Sets.ofFunctor ((CategoryOfElements.π F).leftOp)) := sorry

/-- The raw category-of-elements map preserves composition of presheaf morphisms.

Proof strategy: project to underlying based functors and use the definitional object and morphism
formulas for `CategoryOfElements.map (α ≫ β)`. -/
private theorem ofPresheafMap_comp
    {F G H : Cᵒᵖ ⥤ Type w} (α : F ⟶ G) (β : G ⟶ H) :
    ofPresheafMap (α ≫ β) =
      ofPresheafMap α ≫ ofPresheafMap β := sorry

end Implementation

variable (C) in
/-- The discrete Grothendieck construction `F ↦ 𝒮_F` as a functor from set-valued presheaves to
categories fibred in sets over `C`.

The value universe is independent of the base universes. Its category of elements has object
universe `max u w` and inherits the base morphism universe `v`; this is the minimal owner capable
of storing both base objects and values of `F`. The base category is explicit because this global
functor has no value input from which Lean can recover it. -/
@[stacks 02Y2 "Grothendieck construction for presheaves"]
def ofPresheaf :
    (Cᵒᵖ ⥤ Type w) ⥤ FiberedCategoryOver.Sets.{u, v, max u w, v} C where
  obj F := FiberedCategoryOver.Sets.ofFunctor ((CategoryOfElements.π F).leftOp)
  map α := Implementation.ofPresheafMap α
  map_id F := Implementation.ofPresheafMap_id F
  map_comp α β := Implementation.ofPresheafMap_comp α β

/- Axiom audit: object and map data are the explicit category-of-elements construction. Any
`sorryAx` dependency is confined to projection equality and functor laws. -/

end OfPresheafImplementation

/-- The projection of the discrete Grothendieck construction is the opposite
category-of-elements projection. -/
@[simp]
theorem ofPresheaf.obj.p (F : Cᵒᵖ ⥤ Type w) :
    ((ofPresheaf C).obj F).p =
      (CategoryOfElements.π F).leftOp := sorry
/- Proof strategy: unfold the object projection of `ofPresheaf` and apply `ofFunctor.p`. -/

/-- A presheaf morphism acts on discrete Grothendieck constructions by mathlib's canonical
opposite category-of-elements functor. -/
@[simp]
theorem ofPresheaf.map.toFunctor
    {F G : Cᵒᵖ ⥤ Type w} (α : F ⟶ G) :
    (toBasedFunctor ((ofPresheaf C).map α)).toFunctor =
      (CategoryOfElements.map α).op := sorry
/- Proof strategy: unfold only the map projection of `ofPresheaf`; the private owner morphism is
built from `BasedFunctor.ofFunctor (CategoryOfElements.map α).op`. -/

/-- The total category of the discrete Grothendieck construction is the opposite category of
elements. This projection theorem lets consumers state object- and morphism-level formulas without
unfolding the full-subcategory owner. -/
@[simp]
theorem ofPresheaf.obj.total (F : Cᵒᵖ ⥤ Type w) :
    ((ofPresheaf C).obj F).total = F.Elementsᵒᵖ := sorry
/- Proof strategy: unfold the object projection of `ofPresheaf`, `ofFunctor`, and
`BasedCategory.ofFunctor`; the stored total category is definitionally `F.Elementsᵒᵖ`. -/

/-- A presheaf morphism acts on an object of the discrete Grothendieck construction by the
canonical category-of-elements map. -/
@[simp]
theorem ofPresheaf.map.toFunctor.obj
    {F G : Cᵒᵖ ⥤ Type w} (α : F ⟶ G) (x : F.Elementsᵒᵖ) :
    (toBasedFunctor ((ofPresheaf C).map α)).toFunctor.obj x =
      (CategoryOfElements.map α).op.obj x := sorry
/- Proof strategy: evaluate `ofPresheaf.map.toFunctor α` on `x`. -/

/-- A presheaf morphism acts on a morphism of the discrete Grothendieck construction by the
canonical category-of-elements map. -/
@[simp]
theorem ofPresheaf.map.toFunctor.map_apply
    {F G : Cᵒᵖ ⥤ Type w} (α : F ⟶ G)
    {x y : F.Elementsᵒᵖ} (φ : x ⟶ y) :
    (toBasedFunctor ((ofPresheaf C).map α)).toFunctor.map φ =
      (CategoryOfElements.map α).op.map φ := sorry
/- Proof strategy: evaluate the congruence of `ofPresheaf.map.toFunctor α` on `φ`. -/

/-- Evaluate an object of the standard fiber of the discrete Grothendieck construction as an
element of the original presheaf. The fiber equality transports its stored element to the
displayed base object. -/
@[stacks 02Y2 "Grothendieck fiber evaluation",
  stacks 04SI "Grothendieck fiber evaluation"]
def ofPresheaf.fiberToValue (F : Cᵒᵖ ⥤ Type w) (U : C) :
    ((CategoryOfElements.π F).leftOp).Fiber U → F.obj (op U) :=
  fun x => F.map (eqToHom (congrArg op x.2)) x.1.unop.2

/-- Regard an element of a presheaf value as the corresponding object in the standard fiber of
its discrete Grothendieck construction. -/
@[stacks 02Y2 "presheaf value as a Grothendieck fiber object",
  stacks 04SI "presheaf value as a Grothendieck fiber object"]
def ofPresheaf.valueToFiber (F : Cᵒᵖ ⥤ Type w) (U : C) :
    F.obj (op U) → ((CategoryOfElements.π F).leftOp).Fiber U :=
  fun x => ⟨op ⟨op U, x⟩, rfl⟩

/-- Converting a Grothendieck fiber object to a presheaf value and back recovers the fiber object. -/
theorem ofPresheaf.valueToFiber.leftInverse (F : Cᵒᵖ ⥤ Type w) (U : C) :
    Function.LeftInverse (ofPresheaf.valueToFiber F U) (ofPresheaf.fiberToValue F U) := sorry
/- Proof strategy: destruct the fiber object, eliminate its equality to `U`, and apply
`Functor.Elements.ext`; the transported element then reduces by the identity-map law of `F`. -/

/-- Converting a presheaf value to a Grothendieck fiber object and back recovers the value. -/
theorem ofPresheaf.valueToFiber.rightInverse (F : Cᵒᵖ ⥤ Type w) (U : C) :
    Function.RightInverse (ofPresheaf.valueToFiber F U) (ofPresheaf.fiberToValue F U) := sorry
/- Proof strategy: unfold the two conversion functions; all stored equalities are reflexive and
the claim reduces to `F.map_id`. -/

/-- The canonical equivalence between a standard fiber of the discrete Grothendieck construction
and the corresponding value of the original presheaf.

Its two functions are the explicit owners `ofPresheaf.fiberToValue` and
`ofPresheaf.valueToFiber`; only the inverse-law proof fields are deferred. -/
@[stacks 02Y2 "Grothendieck fiber-value equivalence",
  stacks 04SI "Grothendieck fiber-value equivalence"]
def ofPresheaf.fiberEquiv (F : Cᵒᵖ ⥤ Type w) (U : C) :
    ((CategoryOfElements.π F).leftOp).Fiber U ≃ F.obj (op U) where
  toFun := ofPresheaf.fiberToValue F U
  invFun := ofPresheaf.valueToFiber F U
  left_inv := ofPresheaf.valueToFiber.leftInverse F U
  right_inv := ofPresheaf.valueToFiber.rightInverse F U

/- Axiom audit: the forward and inverse functions of `ofPresheaf.fiberEquiv` are explicit and use
neither choice nor `sorryAx`. Its `sorryAx` dependency is confined to the two `Prop`-valued inverse
laws. -/

/-- The forward function of `ofPresheaf.fiberEquiv` is the canonical evaluation of a fiber
object. -/
@[simp]
theorem ofPresheaf.fiberEquiv.apply
    (F : Cᵒᵖ ⥤ Type w) (U : C) (x : ((CategoryOfElements.π F).leftOp).Fiber U) :
    ofPresheaf.fiberEquiv F U x = ofPresheaf.fiberToValue F U x := sorry
/- Proof strategy: unfold only the `toFun` projection of `ofPresheaf.fiberEquiv`. -/

/-- The inverse function of `ofPresheaf.fiberEquiv` sends a value to its tautological
category-of-elements fiber object. -/
@[simp]
theorem ofPresheaf.fiberEquiv.symm_apply
    (F : Cᵒᵖ ⥤ Type w) (U : C) (x : F.obj (op U)) :
    (ofPresheaf.fiberEquiv F U).symm x = ofPresheaf.valueToFiber F U x := sorry
/- Proof strategy: unfold only the `invFun` projection of `ofPresheaf.fiberEquiv`. -/

end FiberedCategoryOver.Sets

end CategoryTheory
