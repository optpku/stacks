module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.Representable.Stack
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Groupoids.Objects
public import ReasLib.CategoryTheory.Inertia.Relative
public import stacks_project.Chap95.Example_95_17_2_Picard

/-!
# Multiplicative group times the Picard stack

The representable stack of `𝔾ₘ[S]` and the explicit product stack
`𝔾ₘ[S] ×_S Pic_{X/S}`, together with the comparison from inertia.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Picard

/-- The representable presheaf of `𝔾ₘ[S]` is a sheaf on `(Sch/S)_fppf`. -/
theorem mulGroupStack_isSheaf (S : Scheme.{u}) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (yoneda.obj (𝔾ₘ[S]).X) :=
  sorry

/-- The stack in groupoids represented by `𝔾ₘ[S]` over `(Sch/S)_fppf`. -/
def mulGroupStack (S : Scheme.{u}) :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S) :=
  (Over.representableStack (Scheme.fppfTopology.over S) (𝔾ₘ[S]).X
    (mulGroupStack_isSheaf S)).toGroupoids

/-- An object of `𝔾ₘ[S] ×_S Pic_{X/S}` is a Picard object together with a `T`-point of `𝔾ₘ[S]`. -/
structure ProductObj {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The underlying Picard object. -/
  pic : Obj f
  /-- The `𝔾ₘ[S]`-point of the test object. -/
  mul : pic.base ⟶ (𝔾ₘ[S]).X

/-- Package a Picard object and a `𝔾ₘ[S]`-point as a product object. -/
def ProductObj.ofPair {X S : Scheme.{u}} {f : X ⟶ S} (pic : Obj f)
    (mul : pic.base ⟶ (𝔾ₘ[S]).X) : ProductObj f where
  pic := pic
  mul := mul

/-- A morphism of product objects is a Picard morphism commuting with the `𝔾ₘ[S]`-points. -/
structure ProductHom {X S : Scheme.{u}} {f : X ⟶ S} (x y : ProductObj f) where
  /-- The underlying Picard morphism. -/
  pic : Hom x.pic y.pic
  /-- The `𝔾ₘ[S]`-points are compatible with the test map. -/
  mul_w : pic.base ≫ y.mul = x.mul

/-- The identity morphism of a product object. -/
def ProductHom.id {X S : Scheme.{u}} {f : X ⟶ S} (x : ProductObj f) :
    ProductHom x x where
  pic := Hom.id x.pic
  mul_w := Category.id_comp _

/-- Composition of product morphisms. -/
def ProductHom.comp {X S : Scheme.{u}} {f : X ⟶ S} {x y z : ProductObj f}
    (α : ProductHom x y) (β : ProductHom y z) : ProductHom x z where
  pic := Hom.compHom α.pic β.pic
  mul_w :=
    Eq.trans (Category.assoc _ _ _)
      (Eq.trans (congrArg (fun k => α.pic.base ≫ k) β.mul_w) α.mul_w)

/-- Product objects form a category. -/
instance productCategory {X S : Scheme.{u}} (f : X ⟶ S) : Category (ProductObj f) where
  Hom := ProductHom
  id := ProductHom.id
  comp := ProductHom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The projection of the product category to `(Sch/S)_fppf`. -/
def ProductObj.p {X S : Scheme.{u}} (f : X ⟶ S) : ProductObj f ⥤ Over S where
  obj x := x.pic.base
  map α := α.pic.base

/-- The first projection of a product object is its `𝔾ₘ[S]`-point. -/
def ProductObj.fst {X S : Scheme.{u}} {f : X ⟶ S} (x : ProductObj f) :
    x.pic.base ⟶ (𝔾ₘ[S]).X :=
  x.mul

/-- The second projection of a product object is its Picard object. -/
def ProductObj.snd {X S : Scheme.{u}} {f : X ⟶ S} (x : ProductObj f) : Obj f :=
  x.pic

/-- The product projection is a stack in groupoids on `(Sch/S)_fppf`. -/
theorem ProductObj.p_isStack {X S : Scheme.{u}} (f : X ⟶ S) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (ProductObj.p f) :=
  sorry

/-- The product stack `𝔾ₘ[S] ×_S Pic_{X/S}` over `(Sch/S)_fppf`. -/
def mulGroupProduct {X S : Scheme.{u}} (f : X ⟶ S) :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjectionWith (Scheme.fppfTopology.over S) (ProductObj.p f)
    (ProductObj.p_isStack f)

/-- The projection of `mulGroupProduct f` is the product projection. -/
theorem mulGroupProduct_p {X S : Scheme.{u}} (f : X ⟶ S) :
    (mulGroupProduct f).p = ProductObj.p f :=
  sorry

/-- Transport global units of `X_T` to global units of `T` by the structure-sheaf isomorphism. -/
def unitsRestrict {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.IsIsoBaseChangeStructurePushforward f] (T : Over S)
    (u : Γ(pullback f T.hom, ⊤)ˣ) : Γ(T.left, ⊤)ˣ :=
  let φ := (pullback.snd f T.hom).commRingSheafPushforwardMap
  { val := (CategoryTheory.inv φ).hom.app (Opposite.op (⊤ : T.left.Opens)) u.val
    inv := (CategoryTheory.inv φ).hom.app (Opposite.op (⊤ : T.left.Opens)) u.inv
    val_inv := sorry
    inv_val := sorry }

/-- The base morphism of a vertical inertia automorphism is the identity. -/
def inertia_aut_base_eq_id {X S : Scheme.{u}} {f : X ⟶ S}
    (ξ : RelativeInertia (p f)) :
    ξ.aut.hom.base = 𝟙 ξ.obj.base :=
  congrArg Iso.hom ξ.mapAut_eq_one

/-- An inertia object of the Picard stack determines an automorphism of its line bundle. -/
def inertiaAutLine {X S : Scheme.{u}} {f : X ⟶ S} (ξ : RelativeInertia (p f)) :
    Aut ξ.obj.line :=
  autOfVertical ξ.aut.hom (inertia_aut_base_eq_id ξ)

/-- The object map of the comparison from Picard inertia to `𝔾ₘ[S] ×_S Pic_{X/S}`. -/
def inertiaMulObj {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.IsIsoBaseChangeStructurePushforward f]
    (ξ : RelativeInertia (p f)) : ProductObj f where
  pic := ξ.obj
  mul :=
    (MultiplicativeGroup.baseChangeHomEquiv S ξ.obj.base).symm
      (unitsRestrict f ξ.obj.base (autToUnits ξ.obj.line ξ.obj.invertible (inertiaAutLine ξ)))

/-- The arrow map of the comparison from Picard inertia to `𝔾ₘ[S] ×_S Pic_{X/S}`. -/
def inertiaMulMap {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.IsIsoBaseChangeStructurePushforward f]
    {ξ η : RelativeInertia (p f)} (φ : ξ ⟶ η) :
    ProductHom (inertiaMulObj f ξ) (inertiaMulObj f η) where
  pic := RelativeInertia.hom φ
  mul_w := sorry

/-- The total functor of the comparison from Picard inertia to `𝔾ₘ[S] ×_S Pic_{X/S}`. -/
def inertiaMulFunctor {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.IsIsoBaseChangeStructurePushforward f] :
    RelativeInertia (p f) ⥤ ProductObj f where
  obj := inertiaMulObj f
  map := inertiaMulMap f
  map_id := sorry
  map_comp := sorry

/-- The based functor of the comparison from Picard inertia to `𝔾ₘ[S] ×_S Pic_{X/S}`. -/
def inertiaMulBasedFunctor {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.IsIsoBaseChangeStructurePushforward f] :
    (StackOver.Groupoids.inertia (picardStack f)).toBasedCategory ⥤ᵇ
      (mulGroupProduct f).toBasedCategory where
  toFunctor := inertiaMulFunctor f
  w := sorry

/-- The comparison 1-morphism from the inertia stack of `Pic_{X/S}` to
`𝔾ₘ[S] ×_S Pic_{X/S}`. -/
def inertiaMulGroupHom {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.IsIsoBaseChangeStructurePushforward f] :
    StackOver.Groupoids.inertia (picardStack f) ⟶ mulGroupProduct f :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor (inertiaMulBasedFunctor f))

end AlgebraicGeometry.Picard
