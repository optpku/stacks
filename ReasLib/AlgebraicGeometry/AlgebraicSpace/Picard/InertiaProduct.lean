/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Groupoids.Objects
public import ReasLib.CategoryTheory.Inertia.Relative
public import ReasLib.CategoryTheory.Sites.Topos.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSheafSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Stack
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Invertible.Automorphisms
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

/-!
# Multiplicative group times the Picard stack of algebraic spaces

The explicit product stack
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

/-- An object of `𝔾ₘ[S] ×_S Pic_{X/B}` is a Picard object together with a `T`-point of `𝔾ₘ[S]`. -/
structure ProductObject (f : X ⟶ B) where
  /-- The underlying Picard object. -/
  pic : Obj f
  /-- The `𝔾ₘ[S]`-point of the test object. -/
  mul : pic.σ.left ⟶ (𝔾ₘ[S]).X

/-- Package a Picard object and a `𝔾ₘ[S]`-point as a product object. -/
def ProductObject.ofPair {f : X ⟶ B} (pic : Obj f)
    (mul : pic.σ.left ⟶ (𝔾ₘ[S]).X) : ProductObject f where
  pic := pic
  mul := mul

/-- Pairing a Picard object with a multiplicative-group point retains both components. -/
theorem ProductObject.ofPair_spec {f : X ⟶ B} (pic : Obj f)
    (mul : pic.σ.left ⟶ (𝔾ₘ[S]).X) :
    (ProductObject.ofPair pic mul).pic = pic ∧
      (ProductObject.ofPair pic mul).mul = mul := sorry

/-- A morphism of product objects is a Picard morphism commuting with the `𝔾ₘ[S]`-points. -/
structure ProductHom {f : X ⟶ B} (x y : ProductObject f) where
  /-- The underlying Picard morphism. -/
  pic : Hom x.pic y.pic
  /-- The `𝔾ₘ[S]`-points are compatible with the test map. -/
  mul_w : pic.base.left ≫ y.mul = x.mul

/-- A compatible Picard morphism determines a morphism of product objects. -/
def ProductHom.ofPic {f : X ⟶ B} {x y : ProductObject f} (pic : Hom x.pic y.pic)
    (mul_w : pic.base.left ≫ y.mul = x.mul) : ProductHom x y where
  pic := pic
  mul_w := mul_w

/-- A product morphism constructed from a Picard arrow has that arrow and satisfies
compatibility with the multiplicative-group points. -/
theorem ProductHom.ofPic_spec {f : X ⟶ B} {x y : ProductObject f}
    (pic : Hom x.pic y.pic) (mul_w : pic.base.left ≫ y.mul = x.mul) :
    (ProductHom.ofPic pic mul_w).pic = pic ∧
      (ProductHom.ofPic pic mul_w).pic.base.left ≫ y.mul = x.mul := sorry

/-- The identity morphism of a product object. -/
def ProductHom.id {f : X ⟶ B} (x : ProductObject f) : ProductHom x x where
  pic := Hom.id x.pic
  mul_w := Category.id_comp _

/-- Composition of product morphisms. -/
def ProductHom.comp {f : X ⟶ B} {x y z : ProductObject f}
    (α : ProductHom x y) (β : ProductHom y z) : ProductHom x z where
  pic := Hom.comp α.pic β.pic
  mul_w :=
    Eq.trans (Category.assoc _ _ _)
      (Eq.trans (congrArg (fun k => α.pic.base.left ≫ k) β.mul_w) α.mul_w)

/-- Left composition with an identity leaves a product morphism unchanged. -/
theorem ProductHom.id_comp {f : X ⟶ B} {x y : ProductObject f} (α : ProductHom x y) :
    ProductHom.comp (ProductHom.id x) α = α := sorry

/-- Right composition with an identity leaves a product morphism unchanged. -/
theorem ProductHom.comp_id {f : X ⟶ B} {x y : ProductObject f} (α : ProductHom x y) :
    ProductHom.comp α (ProductHom.id y) = α := sorry

/-- Composition of product morphisms is associative. -/
theorem ProductHom.assoc {f : X ⟶ B} {w x y z : ProductObject f}
    (α : ProductHom w x) (β : ProductHom x y) (γ : ProductHom y z) :
    ProductHom.comp (ProductHom.comp α β) γ = ProductHom.comp α (ProductHom.comp β γ) := sorry

/-- The category of Picard objects paired with multiplicative-group points. -/
def productCategory (f : X ⟶ B) : Cat.{u + 1, u + 1} :=
  ⟨ProductObject f, {
    Hom := ProductHom
    id := ProductHom.id
    comp := ProductHom.comp
    id_comp := ProductHom.id_comp
    comp_id := ProductHom.comp_id
    assoc := ProductHom.assoc
  }⟩

/-- The carrier of the category of Picard objects paired with multiplicative-group points. -/
abbrev ProductObj (f : X ⟶ B) : Type (u + 1) := productCategory f

/-- The projection of the product category to schemes over the base scheme. -/
def ProductObj.p (f : X ⟶ B) : ProductObj f ⥤ Over S where
  obj x := x.pic.σ.left
  map α := α.pic.base.left
  map_id x := pMapId x.pic
  map_comp α β := pMapComp α.pic β.pic

/-- The product projection is a stack in groupoids on `(Sch/S)_fppf`. -/
instance ProductObj.p_isStack (f : X ⟶ B) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (ProductObj.p f) := sorry

/-- The product stack `𝔾ₘ[S] ×_S Pic_{X/B}` over `(Sch/S)_fppf`. -/
def mulGroupProduct (f : X ⟶ B) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjectionWith (Scheme.fppfTopology.over S) (ProductObj.p f)
    (ProductObj.p_isStack f)

/-- Evaluation of `O_T` at `smallEtaleSite.id T` recovers the global-sections ring of `T`. -/
private theorem structureSheaf_id_eq (T : Over S) :
    (structureSheaf (ofOver T)).obj.obj (Opposite.op (smallEtaleSite.id T)) =
      (forget₂ CommRingCat RingCat).obj Γ(T.left, ⊤) :=
  rfl

/-- The ring of sections of `f_{T,*} O_{X_T}` at the identity object of `T_étale`. -/
private abbrev pushforwardStructureRing (f : X ⟶ B) (τ : CohStack.SchemesOver B) : RingCat.{u} :=
  ((ringPushforward (CohStack.fiberToBase f τ)).obj
      (structureSheaf (CohStack.fiber f τ))).obj.obj
    (Opposite.op (smallEtaleSite.id τ.left))

/-- Transport global units of `f_{T,*} O_{X_T}` to global units of `T` by the structure-sheaf
isomorphism, evaluated at `smallEtaleSite.id T`. -/
private def unitsRestrict (f : X ⟶ B) [Hom.IsIsoBaseChangeStructurePushforward f]
    (τ : CohStack.SchemesOver B) (u : (pushforwardStructureRing f τ : Type u)ˣ) :
    Γ(τ.left.left, ⊤)ˣ :=
  let φ := structureSheafMap (CohStack.fiberToBase f τ)
  let ψ := CategoryTheory.inv φ
  let V := Opposite.op (smallEtaleSite.id τ.left)
  let e := eqToHom (structureSheaf_id_eq τ.left)
  Units.map (e.hom.comp (ψ.hom.app V).hom).toMonoidHom u

/-- An automorphism of a Picard object lying over the identity of `T` induces an automorphism of
its line bundle. -/
def autOfVertical {f : X ⟶ B} {x : Obj f} (α : Hom x x)
    (hbase : α.base = 𝟙 x.σ) : Aut x.line :=
  α.iso.symm ≪≫
    eqToIso (congrArg (fun h ↦ (Modules.pullback (CohStack.fiberMap f h)).obj x.line) hbase) ≪≫
    Hom.idIso x

/-- The type-valued sheaf of the structure module is the forgotten structure sheaf. -/
private def unitUnderlyingIso (Y : AlgebraicSpace S) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Y)).obj
      (SheafOfModules.unit (structureSheaf Y)) ≅
    (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).obj (structureSheaf Y) :=
  Iso.refl _

/-- Direct image of the structure module on `X_T`, as a type-valued sheaf on `T_étale`. -/
private def pushforwardUnitType (f : X ⟶ B) (τ : CohStack.SchemesOver B) :
    Sheaf (smallEtaleTopology (ofOver τ.left)) (Type u) :=
  (ringedToposHom (CohStack.fiberToBase f τ)).toTopos.pushforward.obj
    ((Sheaf.InternalModule.ToInternal.underlying
        (structureSheaf (CohStack.fiber f τ))).obj
      (SheafOfModules.unit (structureSheaf (CohStack.fiber f τ))))

/-- Evaluation of the direct image of the structure module in the pushforward ring. -/
private def pushforwardUnitEval (f : X ⟶ B) (τ : CohStack.SchemesOver B)
    (x : (pushforwardUnitType f τ).obj.obj (Opposite.op (smallEtaleSite.id τ.left))) :
    (pushforwardStructureRing f τ : Type u) :=
  ((ringPushforwardForgetIso (CohStack.fiberToBase f τ)).inv.app
      (structureSheaf (CohStack.fiber f τ))).hom.app
    (Opposite.op (smallEtaleSite.id τ.left))
    (((ringedToposHom (CohStack.fiberToBase f τ)).toTopos.pushforward.map
        (unitUnderlyingIso (CohStack.fiber f τ)).hom).hom.app
      (Opposite.op (smallEtaleSite.id τ.left)) x)

/-- A section of the pushforward ring gives a section of the direct-image structure module. -/
private def pushforwardUnitEvalInv (f : X ⟶ B) (τ : CohStack.SchemesOver B)
    (y : (pushforwardStructureRing f τ : Type u)) :
    (pushforwardUnitType f τ).obj.obj (Opposite.op (smallEtaleSite.id τ.left)) :=
  (((ringedToposHom (CohStack.fiberToBase f τ)).toTopos.pushforward.map
      (unitUnderlyingIso (CohStack.fiber f τ)).inv).hom.app
    (Opposite.op (smallEtaleSite.id τ.left))
    (((ringPushforwardForgetIso (CohStack.fiberToBase f τ)).hom.app
        (structureSheaf (CohStack.fiber f τ))).hom.app
      (Opposite.op (smallEtaleSite.id τ.left)) y))

/-- Evaluation followed by its inverse recovers a direct-image module section. -/
private theorem pushforwardUnitEvalEquiv_left_inv (f : X ⟶ B) (τ : CohStack.SchemesOver B) :
    Function.LeftInverse (pushforwardUnitEvalInv f τ) (pushforwardUnitEval f τ) := sorry

/-- The inverse evaluation followed by evaluation recovers a pushforward ring section. -/
private theorem pushforwardUnitEvalEquiv_right_inv (f : X ⟶ B) (τ : CohStack.SchemesOver B) :
    Function.RightInverse (pushforwardUnitEvalInv f τ) (pushforwardUnitEval f τ) := sorry

/-- Evaluation identifies direct-image structure-module sections with pushforward ring sections. -/
private def pushforwardUnitEvalEquiv (f : X ⟶ B) (τ : CohStack.SchemesOver B) :
    (pushforwardUnitType f τ).obj.obj (Opposite.op (smallEtaleSite.id τ.left)) ≃
      (pushforwardStructureRing f τ : Type u) where
  toFun := pushforwardUnitEval f τ
  invFun := pushforwardUnitEvalInv f τ
  left_inv := pushforwardUnitEvalEquiv_left_inv f τ
  right_inv := pushforwardUnitEvalEquiv_right_inv f τ

/-- The forward map of `pushforwardUnitEvalEquiv` is evaluation of the forgotten
direct-image structure sheaf. -/
private theorem pushforwardUnitEvalEquiv_apply (f : X ⟶ B) (τ : CohStack.SchemesOver B)
    (x : (pushforwardUnitType f τ).obj.obj (Opposite.op (smallEtaleSite.id τ.left))) :
    pushforwardUnitEvalEquiv f τ x =
      ((ringPushforwardForgetIso (CohStack.fiberToBase f τ)).inv.app
          (structureSheaf (CohStack.fiber f τ))).hom.app
        (Opposite.op (smallEtaleSite.id τ.left))
        (((ringedToposHom (CohStack.fiberToBase f τ)).toTopos.pushforward.map
            (unitUnderlyingIso (CohStack.fiber f τ)).hom).hom.app
          (Opposite.op (smallEtaleSite.id τ.left)) x) :=
  rfl

/-- The scalar section obtained by evaluating the action on the structure module. -/
private def autToUnitsVal (f : X ⟶ B) (τ : CohStack.SchemesOver B)
    (β : Aut (SheafOfModules.unit (structureSheaf (CohStack.fiber f τ)))) :
    (pushforwardStructureRing f τ : Type u) :=
  let M := SheafOfModules.unit (structureSheaf (CohStack.fiber f τ))
  let g := ringedToposHom (CohStack.fiberToBase f τ)
  let V := Opposite.op (smallEtaleSite.id τ.left)
  let e := pushforwardUnitEvalEquiv f τ
  let s (β : Aut M) :=
    (g.toTopos.pushforwardSectionsEquiv
        ((Sheaf.InternalModule.ToInternal.underlying
            (structureSheaf (CohStack.fiber f τ))).obj M)).symm
      ((Sheaf.InternalModule.ToInternal.sectionsEquiv (structureSheaf (CohStack.fiber f τ))
          M).symm (M.unitHomEquiv (Aut.toEnd _ β)))
  e ((s β).val V)

/-- Scalars extracted from an automorphism and its inverse multiply to one. -/
private theorem autToUnits_val_inv {f : X ⟶ B} {x : Obj f} (α : Aut x.line) :
    autToUnitsVal f x.σ (Modules.autToUnitAut x.line x.invertible α) *
      autToUnitsVal f x.σ (Modules.autToUnitAut x.line x.invertible α).symm = 1 := sorry

/-- Scalars extracted from an inverse automorphism and the automorphism multiply to one. -/
private theorem autToUnits_inv_val {f : X ⟶ B} {x : Obj f} (α : Aut x.line) :
    autToUnitsVal f x.σ (Modules.autToUnitAut x.line x.invertible α).symm *
      autToUnitsVal f x.σ (Modules.autToUnitAut x.line x.invertible α) = 1 := sorry

/-- An automorphism of an invertible module determines a unit of the pushforward structure ring. -/
private def autToUnits {f : X ⟶ B} {x : Obj f} (α : Aut x.line) :
    (pushforwardStructureRing f x.σ : Type u)ˣ where
  val := autToUnitsVal f x.σ (Modules.autToUnitAut x.line x.invertible α)
  inv := autToUnitsVal f x.σ (Modules.autToUnitAut x.line x.invertible α).symm
  val_inv := autToUnits_val_inv α
  inv_val := autToUnits_inv_val α

/-- The identity automorphism of a fibrewise line bundle determines the unit `1`. -/
private theorem autToUnits_id {f : X ⟶ B} (x : Obj f) :
    autToUnits (Iso.refl x.line) = 1 := sorry

/-- The base morphism of a vertical inertia automorphism is the identity. -/
private theorem inertia_aut_base_eq_id {f : X ⟶ B} (ξ : RelativeInertia (p f)) :
    ξ.aut.hom.base = 𝟙 ξ.obj.σ :=
  CostructuredArrow.hom_ext ξ.aut.hom.base (𝟙 ξ.obj.σ)
    (congrArg Iso.hom ξ.mapAut_eq_one)

/-- An inertia object of the Picard stack determines an automorphism of its line bundle. -/
private def inertiaAutLine {f : X ⟶ B} (ξ : RelativeInertia (p f)) : Aut ξ.obj.line :=
  autOfVertical ξ.aut.hom (inertia_aut_base_eq_id ξ)

/-- The object map of the comparison from Picard inertia to `𝔾ₘ[S] ×_S Pic_{X/B}`. -/
@[no_expose] def inertiaMulObj (f : X ⟶ B) [Hom.IsIsoBaseChangeStructurePushforward f]
    (ξ : RelativeInertia (p f)) : ProductObj f :=
  ProductObject.ofPair ξ.obj
    ((MultiplicativeGroup.baseChangeHomEquiv S ξ.obj.σ.left).symm
      (unitsRestrict f ξ.obj.σ (autToUnits (inertiaAutLine ξ))))

/-- The scalar points of inertia objects commute with every inertia arrow. -/
private theorem inertiaMulMap_mul_w (f : X ⟶ B) [Hom.IsIsoBaseChangeStructurePushforward f]
    {ξ η : RelativeInertia (p f)} (φ : ξ ⟶ η) :
    (RelativeInertia.hom φ).base.left ≫ (inertiaMulObj f η).mul =
      (inertiaMulObj f ξ).mul := sorry

/-- The arrow map of the comparison from Picard inertia to `𝔾ₘ[S] ×_S Pic_{X/B}`. -/
@[no_expose] def inertiaMulMap (f : X ⟶ B) [Hom.IsIsoBaseChangeStructurePushforward f]
    {ξ η : RelativeInertia (p f)} (φ : ξ ⟶ η) :
    ProductHom (inertiaMulObj f ξ) (inertiaMulObj f η) where
  pic := RelativeInertia.hom φ
  mul_w := inertiaMulMap_mul_w f φ

/-- The comparison on inertia arrows preserves identity morphisms. -/
private theorem inertiaMulMap_id (f : X ⟶ B) [Hom.IsIsoBaseChangeStructurePushforward f]
    (ξ : RelativeInertia (p f)) :
    inertiaMulMap f (𝟙 ξ) = ProductHom.id (inertiaMulObj f ξ) := sorry

/-- The comparison on inertia arrows preserves composition. -/
private theorem inertiaMulMap_comp (f : X ⟶ B) [Hom.IsIsoBaseChangeStructurePushforward f]
    {ξ η ζ : RelativeInertia (p f)} (φ : ξ ⟶ η) (ψ : η ⟶ ζ) :
    inertiaMulMap f (φ ≫ ψ) = ProductHom.comp (inertiaMulMap f φ) (inertiaMulMap f ψ) := sorry

/-- The total functor of the comparison from Picard inertia to `𝔾ₘ[S] ×_S Pic_{X/B}`. -/
@[no_expose] def inertiaMulFunctor (f : X ⟶ B) [Hom.IsIsoBaseChangeStructurePushforward f] :
    RelativeInertia (p f) ⥤ ProductObj f where
  obj := inertiaMulObj f
  map := inertiaMulMap f
  map_id := inertiaMulMap_id f
  map_comp := inertiaMulMap_comp f

/-- The inertia comparison commutes with the projections to test schemes. -/
private theorem inertiaMulFunctor_w (f : X ⟶ B) [Hom.IsIsoBaseChangeStructurePushforward f] :
    inertiaMulFunctor f ⋙ (mulGroupProduct f).p =
      (StackOver.Groupoids.inertia (picardStack f)).p := sorry

/-- The based functor of the comparison from Picard inertia to `𝔾ₘ[S] ×_S Pic_{X/B}`. -/
@[no_expose] def inertiaMulBasedFunctor (f : X ⟶ B) [Hom.IsIsoBaseChangeStructurePushforward f] :
    (StackOver.Groupoids.inertia (picardStack f)).toBasedCategory ⥤ᵇ
      (mulGroupProduct f).toBasedCategory where
  toFunctor := inertiaMulFunctor f
  w := inertiaMulFunctor_w f

/-- The comparison 1-morphism from the inertia stack of `Pic_{X/B}` to
`𝔾ₘ[S] ×_S Pic_{X/B}`. -/
def inertiaMulGroupHom (f : X ⟶ B) [Hom.IsIsoBaseChangeStructurePushforward f] :
    StackOver.Groupoids.inertia (picardStack f) ⟶ mulGroupProduct f :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor (inertiaMulBasedFunctor f))

end AlgebraicGeometry.AlgebraicSpace.Picard

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a flat, proper, finitely presented morphism whose canonical structure-sheaf map
is an isomorphism after every scheme-valued base change, the scalar comparison identifies
Picard inertia with the product of the multiplicative group and the Picard stack. -/
theorem inertia_mulGroupProduct {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Flat f] [Proper f] [FinitePresentation f] [Hom.IsIsoBaseChangeStructurePushforward f] :
    StackOver.Groupoids.Hom.IsEquivalence (Picard.inertiaMulGroupHom f :
      StackOver.Groupoids.inertia (picardStack f) ⟶ Picard.mulGroupProduct f) := sorry

attribute [instance] inertia_mulGroupProduct

end AlgebraicGeometry.AlgebraicSpace
