/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.AlgebraicGeometry.ConstantGroup
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Big
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Basic
public import ReasLib.CategoryTheory.Sites.Torsor.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmallSheaf
public import ReasLib.AlgebraicGeometry.GroupScheme.RepresentableTorsor

/-!
# Quotient stack of an algebraic space by an abstract group

This module records the stack in groupoids `[[X/G]]` attached to an algebraic
space `X` over `S` equipped with a homomorphism `G →* Aut X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace (toSmallSheaf)

noncomputable section

universe u

namespace AlgebraicGeometry.QuotientStack.AbstractGroup

/-- The functor of locally constant `G`-valued maps is an fppf sheaf. -/
theorem constantGroupSheaf_isSheaf (U : Scheme.{u}) (G : Type u) [Group G] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over U)
      (ConstantGroup.points U (GrpCat.of G)) :=
  (Presheaf.isSheaf_of_iso_iff (ConstantGroup.baseChangePointsIso U (GrpCat.of G))).mp
    (GroupScheme.representableGroup_isSheaf .fppf
      (ConstantGroup.baseChange U (GrpCat.of G)))

/-- The constant sheaf of groups `underline(G)` on `(Sch/U)_fppf`. -/
def constantGroupSheaf (U : Scheme.{u}) (G : Type u) [Group G] :
    Sheaf (Scheme.fppfTopology.over U) GrpCat.{u} where
  obj := ConstantGroup.points U (GrpCat.of G)
  property := constantGroupSheaf_isSheaf U G

/-- The underlying group-valued presheaf of `constantGroupSheaf` is
`ConstantGroup.points`. -/
theorem constantGroupSheaf_obj (U : Scheme.{u}) (G : Type u) [Group G] :
    (constantGroupSheaf U G).obj = ConstantGroup.points U (GrpCat.of G) := rfl

/-- Restriction of an fppf sheaf of types from `(Sch/S)_fppf` to `(Sch/U)_fppf`. -/
def restrict {S : Scheme.{u}} (U : Over S) :
    Sheaf (Scheme.fppfTopology.over S) (Type u) ⥤
      Sheaf (Scheme.fppfTopology.over U.left) (Type u) :=
  (Over.map U.hom).sheafPushforwardContinuous (Type u)
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over S)

/-- Inverse image of an fppf sheaf of types along a morphism in `Over S`. -/
def inverseImage {S : Scheme.{u}} {U U' : Over S} (f : U ⟶ U') :
    Sheaf (Scheme.fppfTopology.over U'.left) (Type u) ⥤
      Sheaf (Scheme.fppfTopology.over U.left) (Type u) :=
  (Over.map f.left).sheafPushforwardContinuous (Type u)
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)

/-- Restriction of an fppf sheaf of groups from `(Sch/S)_fppf` to `(Sch/U)_fppf`. -/
def restrictGrp {S : Scheme.{u}} (U : Over S) :
    Sheaf (Scheme.fppfTopology.over S) GrpCat.{u} ⥤
      Sheaf (Scheme.fppfTopology.over U.left) GrpCat.{u} :=
  (Over.map U.hom).sheafPushforwardContinuous GrpCat.{u}
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over S)

/-- Inverse image along an identity morphism of `Over S` is the identity functor. -/
def inverseImageId {S : Scheme.{u}} (U : Over S) :
    inverseImage (𝟙 U) ≅ 𝟭 (Sheaf (Scheme.fppfTopology.over U.left) (Type u)) :=
  Functor.sheafPushforwardContinuousId' (Over.mapId U.left) (Type u)
    (Scheme.fppfTopology.over U.left)

/-- Inverse image is contravariant for composition in `Over S`. -/
def inverseImageComp {S : Scheme.{u}} {U U' U'' : Over S} (f : U ⟶ U') (g : U' ⟶ U'') :
    inverseImage g ⋙ inverseImage f ≅ inverseImage (f ≫ g) :=
  Functor.sheafPushforwardContinuousComp' (Over.mapComp f.left g.left).symm (Type u)
    (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)
    (Scheme.fppfTopology.over U''.left)

/-- Restricting from `S` to `U'` and then pulling back along `f : U ⟶ U'` is
restriction to `U`. -/
def restrictIso {S : Scheme.{u}} {U U' : Over S} (f : U ⟶ U') :
    restrict U' ⋙ inverseImage f ≅ restrict U :=
  Functor.sheafPushforwardContinuousComp'
    ((Over.mapComp f.left U'.hom).symm ≪≫ Over.mapCongr (f.left ≫ U'.hom) U.hom f.w)
    (Type u) (Scheme.fppfTopology.over U.left) (Scheme.fppfTopology.over U'.left)
    (Scheme.fppfTopology.over S)

variable {S : Scheme.{u}} {G : Type u} [Group G] {X : AlgebraicSpace S}

/-- The automorphism `ρ g` of `X`, as an automorphism of the fppf sheaf of points. -/
def autSheaf (ρ : G →* Aut X) (g : G) : toSmallSheaf X ⟶ toSmallSheaf X :=
  Sheaf.homEquiv.symm ((ρ g).hom : (toSmallSheaf X).obj ⟶ (toSmallSheaf X).obj)

/-- The constant section of `underline(G)` with value `g`. -/
def constSection (U : Scheme.{u}) (G : Type u) [Group G] (V : Over U) (g : G) :
    (constantGroupSheaf U G).obj.obj (op V) :=
  LocallyConstant.const V.left g

/-- The action of a group element on a section of an `underline(G)`-torsor. -/
def torsorAct {U : Scheme.{u}} {G : Type u} [Group G]
    (P : Sheaf.Torsor (constantGroupSheaf U G)) (V : (Over U)ᵒᵖ) (g : G)
    (x : P.carrier.obj.obj V) : P.carrier.obj.obj V :=
  (P.mulAction V.unop).toSMul.smul (constSection U G V.unop g) x

/-- Naturality of translation by a constant section of `underline(G)`. -/
theorem torsorAut_naturality {U : Scheme.{u}} {G : Type u} [Group G]
    (P : Sheaf.Torsor (constantGroupSheaf U G)) (g : G) {V W : (Over U)ᵒᵖ} (f : V ⟶ W) :
    P.carrier.obj.map f ≫ TypeCat.ofHom (torsorAct P W g) =
      TypeCat.ofHom (torsorAct P V g) ≫ P.carrier.obj.map f := sorry

/-- Translation by `g` on the underlying sheaf of an `underline(G)`-torsor. -/
def torsorAut {U : Scheme.{u}} {G : Type u} [Group G]
    (P : Sheaf.Torsor (constantGroupSheaf U G)) (g : G) :
    P.carrier ⟶ P.carrier :=
  Sheaf.homEquiv.symm
    { app := fun V ↦ TypeCat.ofHom (torsorAct P V g)
      naturality := fun _ _ f ↦ torsorAut_naturality P g f }

/-- A sheaf map `φ : P ⟶ X|_U` is `G`-equivariant for the action `ρ`. -/
def IsEquivariant (ρ : G →* Aut X) {U : Over S}
    {P : Sheaf.Torsor (constantGroupSheaf U.left G)}
    (φ : P.carrier ⟶ (restrict U).obj (toSmallSheaf X)) : Prop :=
  ∀ g : G, torsorAut P g ≫ φ = φ ≫ (restrict U).map (autSheaf ρ g)

/-- Equivariance is objectwise intertwining of the `G`-actions. -/
theorem IsEquivariant_iff (ρ : G →* Aut X) {U : Over S}
    {P : Sheaf.Torsor (constantGroupSheaf U.left G)}
    (φ : P.carrier ⟶ (restrict U).obj (toSmallSheaf X)) :
    IsEquivariant ρ φ ↔
      ∀ (V : Over U.left) (g : G) (x : P.carrier.obj.obj (op V)),
        φ.hom.app (op V) (torsorAct P (op V) g x) =
          ((restrict U).map (autSheaf ρ g)).hom.app (op V) (φ.hom.app (op V) x) := sorry

/-- An object of `[[X/G]]`: a scheme `U` over `S`, an `underline(G)`-torsor on
`(Sch/U)_fppf`, and a `G`-equivariant map to `X`. -/
structure ObjData (ρ : G →* Aut X) where
  /-- The underlying scheme over `S`. -/
  U : Over S
  /-- The `underline(G)`-torsor on `(Sch/U)_fppf`. -/
  P : Sheaf.Torsor (constantGroupSheaf U.left G)
  /-- The `G`-equivariant sheaf map `P ⟶ X|_U`. -/
  φ : P.carrier ⟶ (restrict U).obj (toSmallSheaf X)
  /-- The map `φ` intertwines the `G`-actions. -/
  equivariant : IsEquivariant ρ φ

/-- A morphism of `underline(G)`-torsors over a map of schemes is `G`-equivariant. -/
def IsEquivariantIso {U U' : Over S}
    {P : Sheaf.Torsor (constantGroupSheaf U.left G)}
    {P' : Sheaf.Torsor (constantGroupSheaf U'.left G)} (f : U ⟶ U')
    (g : P.carrier ≅ (inverseImage f).obj P'.carrier) : Prop :=
  ∀ γ : G, torsorAut P γ ≫ g.hom = g.hom ≫ (inverseImage f).map (torsorAut P' γ)

/-- The comparison `φ' ∘ g` after transporting `φ'` along `f`. -/
def triangleMap {ρ : G →* Aut X} {ξ ξ' : ObjData ρ} (f : ξ.U ⟶ ξ'.U)
    (g : ξ.P.carrier ≅ (inverseImage f).obj ξ'.P.carrier) :
    ξ.P.carrier ⟶ (restrict ξ.U).obj (toSmallSheaf X) :=
  g.hom ≫ (inverseImage f).map ξ'.φ ≫ (restrictIso f).hom.app (toSmallSheaf X)

/-- A morphism of `[[X/G]]`: a map of schemes over `S` and a `G`-equivariant
isomorphism of torsors compatible with the maps to `X`. -/
structure Hom {ρ : G →* Aut X} (ξ ξ' : ObjData ρ) where
  /-- The underlying morphism of schemes over `S`. -/
  f : ξ.U ⟶ ξ'.U
  /-- The `G`-equivariant isomorphism `P ≅ f⁻¹ P'`. -/
  g : ξ.P.carrier ≅ (inverseImage f).obj ξ'.P.carrier
  /-- The isomorphism `g` is `G`-equivariant. -/
  equivariant : IsEquivariantIso f g
  /-- The triangle identity `φ = φ' ∘ g`. -/
  comm : ξ.φ = triangleMap f g

/-- The identity comparison of torsors is `G`-equivariant. -/
theorem id_equivariant {ρ : G →* Aut X} (ξ : ObjData ρ) :
    IsEquivariantIso (𝟙 ξ.U) ((inverseImageId ξ.U).symm.app ξ.P.carrier) := sorry

/-- The identity comparison satisfies the triangle identity. -/
theorem id_comm {ρ : G →* Aut X} (ξ : ObjData ρ) :
    ξ.φ = triangleMap (𝟙 ξ.U) ((inverseImageId ξ.U).symm.app ξ.P.carrier) := sorry

/-- Identity morphisms of `[[X/G]]` are identity on the underlying scheme and
the identity comparison of torsors. -/
def idHom {ρ : G →* Aut X} (ξ : ObjData ρ) : Hom ξ ξ where
  f := 𝟙 ξ.U
  g := (inverseImageId ξ.U).symm.app ξ.P.carrier
  equivariant := id_equivariant ξ
  comm := id_comm ξ

/-- The composite isomorphism of torsors along a composite of scheme maps. -/
def compIso {ρ : G →* Aut X} {ξ ξ' ξ'' : ObjData ρ} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.P.carrier ≅ (inverseImage (α.f ≫ β.f)).obj ξ''.P.carrier :=
  α.g ≪≫ (inverseImage α.f).mapIso β.g ≪≫
    (inverseImageComp α.f β.f).app ξ''.P.carrier

/-- The composite isomorphism of torsors is `G`-equivariant. -/
theorem comp_equivariant {ρ : G →* Aut X} {ξ ξ' ξ'' : ObjData ρ} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    IsEquivariantIso (α.f ≫ β.f) (compIso α β) := sorry

/-- The composite morphism satisfies the triangle identity. -/
theorem comp_comm {ρ : G →* Aut X} {ξ ξ' ξ'' : ObjData ρ} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.φ = triangleMap (α.f ≫ β.f) (compIso α β) := sorry

/-- Composition of morphisms of `[[X/G]]`. -/
def compHom {ρ : G →* Aut X} {ξ ξ' ξ'' : ObjData ρ} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    Hom ξ ξ'' where
  f := α.f ≫ β.f
  g := compIso α β
  equivariant := comp_equivariant α β
  comm := comp_comm α β

/-- Left identity law for morphisms of `[[X/G]]`. -/
theorem idHom_comp {ρ : G →* Aut X} {ξ ξ' : ObjData ρ} (α : Hom ξ ξ') :
    compHom (idHom ξ) α = α := sorry

/-- Right identity law for morphisms of `[[X/G]]`. -/
theorem compHom_id {ρ : G →* Aut X} {ξ ξ' : ObjData ρ} (α : Hom ξ ξ') :
    compHom α (idHom ξ') = α := sorry

/-- Associativity of composition of morphisms of `[[X/G]]`. -/
theorem assocHom {ρ : G →* Aut X} {ξ₁ ξ₂ ξ₃ ξ₄ : ObjData ρ}
    (α : Hom ξ₁ ξ₂) (β : Hom ξ₂ ξ₃) (γ : Hom ξ₃ ξ₄) :
    compHom (compHom α β) γ = compHom α (compHom β γ) := sorry

/-- The category of constant-group torsors equipped with an equivariant map to an algebraic space. -/
def category (ρ : G →* Aut X) : Cat.{u + 1, u + 1} :=
  ⟨ObjData ρ, {
    Hom := fun ξ ξ' ↦ Hom ξ ξ'
    id := idHom
    comp := compHom
    id_comp := idHom_comp
    comp_id := compHom_id
    assoc := assocHom
  }⟩

/-- The carrier of the category of constant-group torsors with an equivariant map. -/
abbrev Obj (ρ : G →* Aut X) : Type (u + 1) := category ρ

/-- Assemble an object of `[[X/G]]` from a torsor and an equivariant map to `X`. -/
def ofTorsor (ρ : G →* Aut X) {U : Over S}
    (P : Sheaf.Torsor (constantGroupSheaf U.left G))
    (φ : P.carrier ⟶ (restrict U).obj (toSmallSheaf X)) (h : IsEquivariant ρ φ) :
    Obj ρ where
  U := U
  P := P
  φ := φ
  equivariant := h

/-- The constructor of `Obj` stores the supplied scheme, torsor, map, and
equivariance witness. -/
theorem ofTorsor_spec (ρ : G →* Aut X) {U : Over S}
    (P : Sheaf.Torsor (constantGroupSheaf U.left G))
    (φ : P.carrier ⟶ (restrict U).obj (toSmallSheaf X)) (h : IsEquivariant ρ φ) :
    (ofTorsor ρ P φ h).U = U ∧ (ofTorsor ρ P φ h).P = P ∧
      (ofTorsor ρ P φ h).φ = φ ∧ (ofTorsor ρ P φ h).equivariant = h := ⟨rfl, rfl, rfl, rfl⟩

/-- Assemble a morphism of `[[X/G]]` from a scheme map and an equivariant
isomorphism of torsors. -/
def ofIso {ρ : G →* Aut X} {ξ ξ' : Obj ρ} (f : ξ.U ⟶ ξ'.U)
    (g : ξ.P.carrier ≅ (inverseImage f).obj ξ'.P.carrier)
    (h : IsEquivariantIso f g) (w : ξ.φ = triangleMap f g) :
    Hom ξ ξ' where
  f := f
  g := g
  equivariant := h
  comm := w

/-- The constructor of `Hom` stores the supplied scheme map, isomorphism, and
compatibilities. -/
theorem ofIso_spec {ρ : G →* Aut X} {ξ ξ' : Obj ρ} (f : ξ.U ⟶ ξ'.U)
    (g : ξ.P.carrier ≅ (inverseImage f).obj ξ'.P.carrier)
    (h : IsEquivariantIso f g) (w : ξ.φ = triangleMap f g) :
    (ofIso f g h w).f = f ∧ (ofIso f g h w).g = g ∧
      (ofIso f g h w).equivariant = h ∧ (ofIso f g h w).comm = w := ⟨rfl, rfl, rfl, rfl⟩

/-- The forgetful functor sends identity morphisms to identity morphisms. -/
theorem forget_map_id {ρ : G →* Aut X} (ξ : Obj ρ) : (idHom ξ).f = 𝟙 ξ.U := rfl

/-- The forgetful functor preserves composition. -/
theorem forget_map_comp {ρ : G →* Aut X} {ξ ξ' ξ'' : Obj ρ} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (compHom α β).f = α.f ≫ β.f := rfl

/-- The forgetful functor `[[X/G]] ⟶ (Sch/S)_fppf`. -/
def forget (ρ : G →* Aut X) : Obj ρ ⥤ Over S where
  obj ξ := ξ.U
  map α := α.f
  map_id := forget_map_id
  map_comp := forget_map_comp

/-- The forgetful functor sends `(U, P, φ)` to `U`. -/
theorem forget_obj {ρ : G →* Aut X} (ξ : Obj ρ) : (forget ρ).obj ξ = ξ.U := rfl

/-- The forgetful functor sends a morphism `(f, g)` to `f`. -/
theorem forget_map {ρ : G →* Aut X} {ξ ξ' : Obj ρ} (α : Hom ξ ξ') : (forget ρ).map α = α.f := rfl

/-- The forgetful functor `[[X/G]] ⟶ (Sch/S)_fppf` is a stack in groupoids. -/
instance instIsStackInGroupoids (ρ : G →* Aut X) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (forget ρ) := sorry

/-- The stack in groupoids `[[X/G]]` over `(Sch/S)_fppf`. -/
def stack (ρ : G →* Aut X) : StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjection (Scheme.fppfTopology.over S) (forget ρ)

/-- The projection of `stack` is the forgetful functor to `(Sch/S)_fppf`. -/
theorem stack_p (ρ : G →* Aut X) : (stack ρ).p = forget ρ := rfl

end AlgebraicGeometry.QuotientStack.AbstractGroup
