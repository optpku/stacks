/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Endomorphism
public import ReasLib.AlgebraicGeometry.MultiplicativeGroup
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.Representable.Stack
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Groupoids.Objects
public import ReasLib.CategoryTheory.Inertia.Relative
public import ReasLib.CategoryTheory.Sites.Topos.Sections
public import stacks_project.Chap66.Lemma_66_27_3_Space
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower
public import stacks_project.Chap99.Lemma_99_11_7_Pushforward
public import stacks_project.Chap108.Lemma_108_8_4_Stack

/-!
# Multiplicative group times the Picard stack of algebraic spaces

The representable stack of `𝔾ₘ[S]` and the explicit product stack
`𝔾ₘ[S] ×_S Pic_{X/B}`, together with the comparison from inertia.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The representable presheaf of `𝔾ₘ[S]` is a sheaf on `(Sch/S)_fppf`. -/
theorem mulGroupStack_isSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (yoneda.obj (𝔾ₘ[S]).X) :=
  sorry

/-- The stack in groupoids represented by `𝔾ₘ[S]` over `(Sch/S)_fppf`. -/
def mulGroupStack :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  (Over.representableStack (Scheme.fppfTopology.over S) (𝔾ₘ[S]).X
    mulGroupStack_isSheaf).toGroupoids

/-- An object of `𝔾ₘ[S] ×_S Pic_{X/B}` is a Picard object together with a `T`-point of `𝔾ₘ[S]`. -/
structure ProductObj (f : X ⟶ B) where
  /-- The underlying Picard object. -/
  pic : Obj f
  /-- The `𝔾ₘ[S]`-point of the test object. -/
  mul : pic.σ.left ⟶ (𝔾ₘ[S]).X

/-- Package a Picard object and a `𝔾ₘ[S]`-point as a product object. -/
def ProductObj.ofPair {f : X ⟶ B} (pic : Obj f)
    (mul : pic.σ.left ⟶ (𝔾ₘ[S]).X) : ProductObj f where
  pic := pic
  mul := mul

/-- A morphism of product objects is a Picard morphism commuting with the `𝔾ₘ[S]`-points. -/
structure ProductHom {f : X ⟶ B} (x y : ProductObj f) where
  /-- The underlying Picard morphism. -/
  pic : Hom x.pic y.pic
  /-- The `𝔾ₘ[S]`-points are compatible with the test map. -/
  mul_w : pic.base.left ≫ y.mul = x.mul

/-- The identity morphism of a product object. -/
def ProductHom.id {f : X ⟶ B} (x : ProductObj f) : ProductHom x x where
  pic := Hom.id x.pic
  mul_w := Category.id_comp _

/-- Composition of product morphisms. -/
def ProductHom.comp {f : X ⟶ B} {x y z : ProductObj f}
    (α : ProductHom x y) (β : ProductHom y z) : ProductHom x z where
  pic := Hom.comp α.pic β.pic
  mul_w :=
    Eq.trans (Category.assoc _ _ _)
      (Eq.trans (congrArg (fun k => α.pic.base.left ≫ k) β.mul_w) α.mul_w)

/-- Product objects form a category. -/
instance productCategory (f : X ⟶ B) : Category (ProductObj f) where
  Hom := ProductHom
  id := ProductHom.id
  comp := ProductHom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The projection of the product category to `(Sch/S)_fppf`. -/
def ProductObj.p (f : X ⟶ B) : ProductObj f ⥤ Over S where
  obj x := x.pic.σ.left
  map α := α.pic.base.left

/-- The first projection of a product object is its `𝔾ₘ[S]`-point. -/
def ProductObj.fst {f : X ⟶ B} (x : ProductObj f) :
    x.pic.σ.left ⟶ (𝔾ₘ[S]).X :=
  x.mul

/-- The second projection of a product object is its Picard object. -/
def ProductObj.snd {f : X ⟶ B} (x : ProductObj f) : Obj f :=
  x.pic

/-- The product projection is a stack in groupoids on `(Sch/S)_fppf`. -/
theorem ProductObj.p_isStack (f : X ⟶ B) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (ProductObj.p f) :=
  sorry

/-- The product stack `𝔾ₘ[S] ×_S Pic_{X/B}` over `(Sch/S)_fppf`. -/
def mulGroupProduct (f : X ⟶ B) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjectionWith (Scheme.fppfTopology.over S) (ProductObj.p f)
    (ProductObj.p_isStack f)

/-- The projection of `mulGroupProduct f` is the product projection. -/
theorem mulGroupProduct_p (f : X ⟶ B) :
    (mulGroupProduct f).p = ProductObj.p f :=
  sorry

/-- Evaluation of `O_T` at `smallEtaleSite.id T` recovers the global-sections ring of `T`. -/
theorem structureSheaf_id_eq (T : Over S) :
    (structureSheaf (ofOver T)).obj.obj (Opposite.op (smallEtaleSite.id T)) =
      (forget₂ CommRingCat RingCat).obj Γ(T.left, ⊤) :=
  rfl

/-- The ring of sections of `f_{T,*} O_{X_T}` at the identity object of `T_étale`. -/
abbrev pushforwardStructureRing (f : X ⟶ B) (τ : CohStack.SchemesOver B) : RingCat.{u} :=
  ((ringPushforward (CohStack.fiberToBase f τ)).obj
      (structureSheaf (CohStack.fiber f τ))).obj.obj
    (Opposite.op (smallEtaleSite.id τ.left))

/-- `pushforwardStructureRing f τ` is the value of `f_{T,*} O_{X_T}` at `smallEtaleSite.id T`. -/
theorem pushforwardStructureRing_eq (f : X ⟶ B) (τ : CohStack.SchemesOver B) :
    pushforwardStructureRing f τ =
      ((ringPushforward (CohStack.fiberToBase f τ)).obj
          (structureSheaf (CohStack.fiber f τ))).obj.obj
        (Opposite.op (smallEtaleSite.id τ.left)) :=
  rfl

/-- Transport global units of `f_{T,*} O_{X_T}` to global units of `T` by the structure-sheaf
isomorphism, evaluated at `smallEtaleSite.id T`. -/
def unitsRestrict (f : X ⟶ B) [Hom.IsIsoBaseChangeStructurePushforward f]
    (τ : CohStack.SchemesOver B) (u : (pushforwardStructureRing f τ : Type u)ˣ) :
    Γ(τ.left.left, ⊤)ˣ :=
  let φ := structureSheafMap (CohStack.fiberToBase f τ)
  let ψ := CategoryTheory.inv φ
  let V := Opposite.op (smallEtaleSite.id τ.left)
  let e := eqToHom (structureSheaf_id_eq τ.left)
  { val := e.hom ((ψ.hom.app V).hom u.val)
    inv := e.hom ((ψ.hom.app V).hom u.inv)
    val_inv := sorry
    inv_val := sorry }

/-- An automorphism of a Picard object lying over the identity of `T` induces an automorphism of
its line bundle. -/
def autOfVertical {f : X ⟶ B} {x : Obj f} (α : Hom x x)
    (hbase : α.base = 𝟙 x.σ) : Aut x.line :=
  α.iso.symm ≪≫
    eqToIso (congrArg (fun h ↦ (Modules.pullback (CohStack.fiberMap f h)).obj x.line) hbase) ≪≫
    Hom.idIso x

/-- Automorphisms of an invertible module induce automorphisms of the monoidal unit. -/
def autToAutUnit {Y : AlgebraicSpace S} (L : Y.Modules)
    (hL : isInvertibleObject L) (α : Aut L) : Aut (𝟙_ Y.Modules) :=
  (@isInvertibleObject.tensorInverseIso Y.Modules _ _ L hL).conjAut
    ((tensorRight (@isInvertibleObject.inverse Y.Modules _ _ L hL)).mapIso α)

/-- Automorphisms of the monoidal unit induce automorphisms of an invertible module. -/
def autUnitToAut {Y : AlgebraicSpace S} (L : Y.Modules) (β : Aut (𝟙_ Y.Modules)) :
    Aut L :=
  (λ_ L).conjAut ((tensorRight L).mapIso β)

/-- The left inverse law of `autToAutUnit`. -/
theorem autToAutUnit_left {Y : AlgebraicSpace S} (L : Y.Modules)
    (hL : isInvertibleObject L) (α : Aut L) :
    autUnitToAut L (autToAutUnit L hL α) = α :=
  sorry

/-- The right inverse law of `autToAutUnit`. -/
theorem autToAutUnit_right {Y : AlgebraicSpace S} (L : Y.Modules)
    (hL : isInvertibleObject L) (β : Aut (𝟙_ Y.Modules)) :
    autToAutUnit L hL (autUnitToAut L β) = β :=
  sorry

/-- Automorphisms of an invertible module determine automorphisms of the structure module. -/
def autToUnitAut {Y : AlgebraicSpace S} (L : Y.Modules)
    (hL : isInvertibleObject L) (α : Aut L) :
    Aut (SheafOfModules.unit (structureSheaf Y)) :=
  (Modules.structureModuleIsoTensorUnit Y).symm.conjAut (autToAutUnit L hL α)

/-- Automorphisms of the structure module determine automorphisms of an invertible module. -/
def unitAutToAut {Y : AlgebraicSpace S} (L : Y.Modules)
    (β : Aut (SheafOfModules.unit (structureSheaf Y))) : Aut L :=
  autUnitToAut L ((Modules.structureModuleIsoTensorUnit Y).conjAut β)

/-- The type-valued sheaf of the structure module is the forgotten structure sheaf. -/
def unitUnderlyingIso (Y : AlgebraicSpace S) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Y)).obj
      (SheafOfModules.unit (structureSheaf Y)) ≅
    (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).obj (structureSheaf Y) :=
  Iso.refl _

/-- `unitUnderlyingIso` is the identity comparison of underlying type-valued sheaves. -/
theorem unitUnderlyingIso_eq (Y : AlgebraicSpace S) :
    unitUnderlyingIso Y = Iso.refl _ :=
  rfl

/-- Direct image of the structure module on `X_T`, as a type-valued sheaf on `T_étale`. -/
def pushforwardUnitType (f : X ⟶ B) (τ : CohStack.SchemesOver B) :
    Sheaf (smallEtaleTopology (ofOver τ.left)) (Type u) :=
  (ringedToposHom (CohStack.fiberToBase f τ)).toTopos.pushforward.obj
    ((Sheaf.InternalModule.ToInternal.underlying
        (structureSheaf (CohStack.fiber f τ))).obj
      (SheafOfModules.unit (structureSheaf (CohStack.fiber f τ))))

/-- `pushforwardUnitType` is direct image of the underlying structure module. -/
theorem pushforwardUnitType_eq (f : X ⟶ B) (τ : CohStack.SchemesOver B) :
    pushforwardUnitType f τ =
      (ringedToposHom (CohStack.fiberToBase f τ)).toTopos.pushforward.obj
        ((Sheaf.InternalModule.ToInternal.underlying
            (structureSheaf (CohStack.fiber f τ))).obj
          (SheafOfModules.unit (structureSheaf (CohStack.fiber f τ)))) :=
  rfl

/-- Evaluation of the direct image of the structure module at `smallEtaleSite.id T`
is equivalent to the ring of sections of `f_{T,*} O_{X_T}`. -/
def pushforwardUnitEvalEquiv (f : X ⟶ B) (τ : CohStack.SchemesOver B) :
    (pushforwardUnitType f τ).obj.obj (Opposite.op (smallEtaleSite.id τ.left)) ≃
      (pushforwardStructureRing f τ : Type u) where
  toFun x :=
    ((ringPushforwardForgetIso (CohStack.fiberToBase f τ)).inv.app
        (structureSheaf (CohStack.fiber f τ))).hom.app
      (Opposite.op (smallEtaleSite.id τ.left))
      (((ringedToposHom (CohStack.fiberToBase f τ)).toTopos.pushforward.map
          (unitUnderlyingIso (CohStack.fiber f τ)).hom).hom.app
        (Opposite.op (smallEtaleSite.id τ.left)) x)
  invFun y :=
    (((ringedToposHom (CohStack.fiberToBase f τ)).toTopos.pushforward.map
        (unitUnderlyingIso (CohStack.fiber f τ)).inv).hom.app
      (Opposite.op (smallEtaleSite.id τ.left))
      (((ringPushforwardForgetIso (CohStack.fiberToBase f τ)).hom.app
          (structureSheaf (CohStack.fiber f τ))).hom.app
        (Opposite.op (smallEtaleSite.id τ.left)) y))
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `pushforwardUnitEvalEquiv` is evaluation of the forgotten
direct-image structure sheaf. -/
theorem pushforwardUnitEvalEquiv_apply (f : X ⟶ B) (τ : CohStack.SchemesOver B)
    (x : (pushforwardUnitType f τ).obj.obj (Opposite.op (smallEtaleSite.id τ.left))) :
    pushforwardUnitEvalEquiv f τ x =
      ((ringPushforwardForgetIso (CohStack.fiberToBase f τ)).inv.app
          (structureSheaf (CohStack.fiber f τ))).hom.app
        (Opposite.op (smallEtaleSite.id τ.left))
        (((ringedToposHom (CohStack.fiberToBase f τ)).toTopos.pushforward.map
            (unitUnderlyingIso (CohStack.fiber f τ)).hom).hom.app
          (Opposite.op (smallEtaleSite.id τ.left)) x) :=
  rfl

/-- Automorphisms of an invertible module on a fibre determine units of
`f_{T,*} O_{X_T}` at `smallEtaleSite.id T`. -/
def autToUnits {f : X ⟶ B} {x : Obj f} (α : Aut x.line) :
    (pushforwardStructureRing f x.σ : Type u)ˣ :=
  let M := SheafOfModules.unit (structureSheaf (CohStack.fiber f x.σ))
  let g := ringedToposHom (CohStack.fiberToBase f x.σ)
  let V := Opposite.op (smallEtaleSite.id x.σ.left)
  let e := pushforwardUnitEvalEquiv f x.σ
  let s (β : Aut M) :=
    (g.toTopos.pushforwardSectionsEquiv
        ((Sheaf.InternalModule.ToInternal.underlying
            (structureSheaf (CohStack.fiber f x.σ))).obj M)).symm
      ((Sheaf.InternalModule.ToInternal.sectionsEquiv (structureSheaf (CohStack.fiber f x.σ))
          M).symm (M.unitHomEquiv (Aut.toEnd _ β)))
  { val := e ((s (autToUnitAut x.line x.invertible α)).val V)
    inv := e ((s (autToUnitAut x.line x.invertible α).symm).val V)
    val_inv := sorry
    inv_val := sorry }

/-- The identity automorphism of a fibrewise line bundle determines the unit `1`. -/
theorem autToUnits_id {f : X ⟶ B} (x : Obj f) :
    autToUnits (Iso.refl x.line) = 1 :=
  sorry

/-- The base morphism of a vertical inertia automorphism is the identity. -/
def inertia_aut_base_eq_id {f : X ⟶ B} (ξ : RelativeInertia (p f)) :
    ξ.aut.hom.base = 𝟙 ξ.obj.σ :=
  CostructuredArrow.hom_ext ξ.aut.hom.base (𝟙 ξ.obj.σ)
    (congrArg Iso.hom ξ.mapAut_eq_one)

/-- An inertia object of the Picard stack determines an automorphism of its line bundle. -/
def inertiaAutLine {f : X ⟶ B} (ξ : RelativeInertia (p f)) : Aut ξ.obj.line :=
  autOfVertical ξ.aut.hom (inertia_aut_base_eq_id ξ)

/-- The object map of the comparison from Picard inertia to `𝔾ₘ[S] ×_S Pic_{X/B}`. -/
def inertiaMulObj (f : X ⟶ B) [Hom.IsIsoBaseChangeStructurePushforward f]
    (ξ : RelativeInertia (p f)) : ProductObj f :=
  ProductObj.ofPair ξ.obj
    ((MultiplicativeGroup.baseChangeHomEquiv S ξ.obj.σ.left).symm
      (unitsRestrict f ξ.obj.σ (autToUnits (inertiaAutLine ξ))))

/-- The arrow map of the comparison from Picard inertia to `𝔾ₘ[S] ×_S Pic_{X/B}`. -/
def inertiaMulMap (f : X ⟶ B) [Hom.IsIsoBaseChangeStructurePushforward f]
    {ξ η : RelativeInertia (p f)} (φ : ξ ⟶ η) :
    ProductHom (inertiaMulObj f ξ) (inertiaMulObj f η) where
  pic := RelativeInertia.hom φ
  mul_w := sorry

/-- The total functor of the comparison from Picard inertia to `𝔾ₘ[S] ×_S Pic_{X/B}`. -/
def inertiaMulFunctor (f : X ⟶ B) [Hom.IsIsoBaseChangeStructurePushforward f] :
    RelativeInertia (p f) ⥤ ProductObj f where
  obj := inertiaMulObj f
  map := inertiaMulMap f
  map_id := sorry
  map_comp := sorry

/-- The based functor of the comparison from Picard inertia to `𝔾ₘ[S] ×_S Pic_{X/B}`. -/
def inertiaMulBasedFunctor (f : X ⟶ B) [Hom.IsIsoBaseChangeStructurePushforward f] :
    (StackOver.Groupoids.inertia (picardStack f)).toBasedCategory ⥤ᵇ
      (mulGroupProduct f).toBasedCategory where
  toFunctor := inertiaMulFunctor f
  w := sorry

/-- The comparison 1-morphism from the inertia stack of `Pic_{X/B}` to
`𝔾ₘ[S] ×_S Pic_{X/B}`. -/
def inertiaMulGroupHom (f : X ⟶ B) [Hom.IsIsoBaseChangeStructurePushforward f] :
    StackOver.Groupoids.inertia (picardStack f) ⟶ mulGroupProduct f :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor (inertiaMulBasedFunctor f))


end AlgebraicGeometry.AlgebraicSpace.Picard
