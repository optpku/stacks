/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.GroupScheme.RepresentableTorsor
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Equivalence
public import ReasLib.AlgebraicGeometry.QuotientStack.AbstractGroup
public import ReasLib.CategoryTheory.Sites.Torsor.Transport
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso

/-!
# Comparison of `[[X/G]]` with the quotient by the constant group scheme `G_S`

This module records the sheaf-level stack `[[X/G_S]]` and the identification of
the constant sheaf `underline(G)` with the functor of points of `G_S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace (toSmallSheaf)
open AlgebraicGeometry.QuotientStack.AbstractGroup
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.QuotientStack.BaseChange

/-- The constant sheaf `underline(G)` is represented by `G_S` on `(Sch/S)_fppf`.
The common universe of `G` and `S` is the smallness restriction for the coproduct scheme. -/
theorem constantSheaf_represented (S : Scheme.{u}) (G : GrpCat.{u}) :
    IsIsomorphic (constantGroupSheaf S G).obj
      (yonedaGrp.obj (ConstantGroup.baseChange S G)) :=
  ⟨(ConstantGroup.baseChangePointsIso S G).symm⟩

variable {S : Scheme.{u}} {G : Type u} [Group G] {X : AlgebraicSpace S}

/-- The constant `G_S`-valued map associated to an abstract group element. -/
def constSection (U : Over S) (V : Over U.left) (g : G) :
    ((restrictGrp U).obj (GroupScheme.representableGroup .fppf (ConstantGroup.baseChange S (GrpCat.of G)))).obj.obj (op V) :=
  (ConstantGroup.baseChangeHomEquiv S (GrpCat.of G) ((Over.map U.hom).obj V)).symm
    (LocallyConstant.const ((Over.map U.hom).obj V).left g)

/-- The action of a group element on a section of a `G_S`-torsor. -/
def torsorAct {U : Over S}
    (P : Sheaf.Torsor ((restrictGrp U).obj (GroupScheme.representableGroup .fppf (ConstantGroup.baseChange S (GrpCat.of G)))))
    (V : (Over U.left)ᵒᵖ) (g : G) (x : P.carrier.obj.obj V) :
    P.carrier.obj.obj V :=
  (P.mulAction V.unop).toSMul.smul (constSection U V.unop g) x

/-- Naturality of translation by a constant section of `G_S`. -/
theorem torsorAut_naturality {U : Over S}
    (P : Sheaf.Torsor ((restrictGrp U).obj (GroupScheme.representableGroup .fppf (ConstantGroup.baseChange S (GrpCat.of G))))) (g : G)
    {V W : (Over U.left)ᵒᵖ} (f : V ⟶ W) :
    P.carrier.obj.map f ≫ TypeCat.ofHom (torsorAct P W g) =
      TypeCat.ofHom (torsorAct P V g) ≫ P.carrier.obj.map f := sorry

/-- Translation by `g` on the underlying sheaf of a `G_S`-torsor. -/
def torsorAut {U : Over S}
    (P : Sheaf.Torsor ((restrictGrp U).obj (GroupScheme.representableGroup .fppf (ConstantGroup.baseChange S (GrpCat.of G))))) (g : G) :
    P.carrier ⟶ P.carrier :=
  Sheaf.homEquiv.symm
    { app := fun V ↦ TypeCat.ofHom (torsorAct P V g)
      naturality := fun _ _ f ↦ torsorAut_naturality P g f }

/-- A sheaf map `φ : P ⟶ X|_U` is `G`-equivariant for the action `ρ`. -/
def IsEquivariant (ρ : G →* Aut X) {U : Over S}
    {P : Sheaf.Torsor ((restrictGrp U).obj (GroupScheme.representableGroup .fppf (ConstantGroup.baseChange S (GrpCat.of G))))}
    (φ : P.carrier ⟶ (restrict U).obj (toSmallSheaf X)) : Prop :=
  ∀ g : G, torsorAut P g ≫ φ = φ ≫ (restrict U).map (autSheaf ρ g)

/-- Equivariance on constant elements is equivalent to equivariance on every represented
section after restricting to the open fibres of its locally constant value map. On the fibre
indexed by `g`, the induced constant-group-scheme action on the target is precisely `ρ g`. -/
theorem isEquivariant_iff_locallyConstant (ρ : G →* Aut X) {U : Over S}
    {P : Sheaf.Torsor ((restrictGrp U).obj
      (GroupScheme.representableGroup .fppf (ConstantGroup.baseChange S (GrpCat.of G))))}
    (φ : P.carrier ⟶ (restrict U).obj (toSmallSheaf X)) :
    IsEquivariant ρ φ ↔
      ∀ (V : Over U.left)
        (s : ((restrictGrp U).obj
          (GroupScheme.representableGroup .fppf (ConstantGroup.baseChange S (GrpCat.of G)))).obj.obj
            (op V)) (x : P.carrier.obj.obj (op V)) (g : G),
        let a := ConstantGroup.baseChangeHomEquiv S (GrpCat.of G) ((Over.map U.hom).obj V) s
        let cover := ConstantGroup.fiberCover (GrpCat.of G) ((Over.map U.hom).obj V) a
        let W : Over U.left := Over.mk (cover.f g ≫ V.hom)
        let ι : W ⟶ V := Over.homMk (cover.f g) rfl
        φ.hom.app (op W) (P.carrier.obj.map ι.op ((P.mulAction V).smul s x)) =
          ((restrict U).map (autSheaf ρ g)).hom.app (op W)
            (φ.hom.app (op W) (P.carrier.obj.map ι.op x)) := sorry

/-- An object of `[[X/G_S]]`: a scheme `U` over `S`, a `G_S`-torsor on
`(Sch/U)_fppf`, and a `G`-equivariant map to `X`. -/
structure ObjData (ρ : G →* Aut X) where
  /-- The underlying scheme over `S`. -/
  U : Over S
  /-- The `G_S`-torsor on `(Sch/U)_fppf`. -/
  P : Sheaf.Torsor ((restrictGrp U).obj (GroupScheme.representableGroup .fppf (ConstantGroup.baseChange S (GrpCat.of G))))
  /-- The `G`-equivariant sheaf map `P ⟶ X|_U`. -/
  φ : P.carrier ⟶ (restrict U).obj (toSmallSheaf X)
  /-- The map `φ` intertwines the `G`-actions. -/
  equivariant : IsEquivariant ρ φ

/-- A morphism of `G_S`-torsors over a map of schemes is `G`-equivariant. -/
def IsEquivariantIso {U U' : Over S}
    {P : Sheaf.Torsor ((restrictGrp U).obj (GroupScheme.representableGroup .fppf (ConstantGroup.baseChange S (GrpCat.of G))))}
    {P' : Sheaf.Torsor ((restrictGrp U').obj (GroupScheme.representableGroup .fppf (ConstantGroup.baseChange S (GrpCat.of G))))}
    (f : U ⟶ U') (g : P.carrier ≅ (inverseImage f).obj P'.carrier) : Prop :=
  ∀ γ : G, torsorAut P γ ≫ g.hom = g.hom ≫ (inverseImage f).map (torsorAut P' γ)

/-- The comparison `φ' ∘ g` after transporting `φ'` along `f`. -/
def triangleMap {ρ : G →* Aut X} {ξ ξ' : ObjData ρ} (f : ξ.U ⟶ ξ'.U)
    (g : ξ.P.carrier ≅ (inverseImage f).obj ξ'.P.carrier) :
    ξ.P.carrier ⟶ (restrict ξ.U).obj (toSmallSheaf X) :=
  g.hom ≫ (inverseImage f).map ξ'.φ ≫ (restrictIso f).hom.app (toSmallSheaf X)

/-- A morphism of `[[X/G_S]]`. -/
structure Hom {ρ : G →* Aut X} (ξ ξ' : ObjData ρ) where
  /-- The underlying morphism of schemes over `S`. -/
  f : ξ.U ⟶ ξ'.U
  /-- The `G`-equivariant isomorphism `P ≅ f⁻¹ P'`. -/
  g : ξ.P.carrier ≅ (inverseImage f).obj ξ'.P.carrier
  /-- The isomorphism `g` is `G`-equivariant. -/
  equivariant : IsEquivariantIso f g
  /-- The triangle identity `φ = φ' ∘ g`. -/
  comm : ξ.φ = triangleMap f g

/-- The identity comparison of `G_S`-torsors is `G`-equivariant. -/
theorem id_equivariant {ρ : G →* Aut X} (ξ : ObjData ρ) :
    IsEquivariantIso (𝟙 ξ.U) ((inverseImageId ξ.U).symm.app ξ.P.carrier) := sorry

/-- The identity comparison satisfies the triangle identity. -/
theorem id_comm {ρ : G →* Aut X} (ξ : ObjData ρ) :
    ξ.φ = triangleMap (𝟙 ξ.U) ((inverseImageId ξ.U).symm.app ξ.P.carrier) := sorry

/-- Identity morphisms of `[[X/G_S]]`. -/
def idHom {ρ : G →* Aut X} (ξ : ObjData ρ) : Hom ξ ξ where
  f := 𝟙 ξ.U
  g := (inverseImageId ξ.U).symm.app ξ.P.carrier
  equivariant := id_equivariant ξ
  comm := id_comm ξ

/-- The composite isomorphism of `G_S`-torsors. -/
def compIso {ρ : G →* Aut X} {ξ ξ' ξ'' : ObjData ρ} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.P.carrier ≅ (inverseImage (α.f ≫ β.f)).obj ξ''.P.carrier :=
  α.g ≪≫ (inverseImage α.f).mapIso β.g ≪≫
    (inverseImageComp α.f β.f).app ξ''.P.carrier

/-- The composite isomorphism of `G_S`-torsors is `G`-equivariant. -/
theorem comp_equivariant {ρ : G →* Aut X} {ξ ξ' ξ'' : ObjData ρ}
    (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    IsEquivariantIso (α.f ≫ β.f) (compIso α β) := sorry

/-- The composite morphism satisfies the triangle identity. -/
theorem comp_comm {ρ : G →* Aut X} {ξ ξ' ξ'' : ObjData ρ}
    (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.φ = triangleMap (α.f ≫ β.f) (compIso α β) := sorry

/-- Composition of morphisms of `[[X/G_S]]`. -/
def compHom {ρ : G →* Aut X} {ξ ξ' ξ'' : ObjData ρ} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    Hom ξ ξ'' where
  f := α.f ≫ β.f
  g := compIso α β
  equivariant := comp_equivariant α β
  comm := comp_comm α β

/-- Left identity law for morphisms of `[[X/G_S]]`. -/
theorem idHom_comp {ρ : G →* Aut X} {ξ ξ' : ObjData ρ} (α : Hom ξ ξ') :
    compHom (idHom ξ) α = α := sorry

/-- Right identity law for morphisms of `[[X/G_S]]`. -/
theorem compHom_id {ρ : G →* Aut X} {ξ ξ' : ObjData ρ} (α : Hom ξ ξ') :
    compHom α (idHom ξ') = α := sorry

/-- Associativity of composition of morphisms of `[[X/G_S]]`. -/
theorem assocHom {ρ : G →* Aut X} {ξ₁ ξ₂ ξ₃ ξ₄ : ObjData ρ}
    (α : Hom ξ₁ ξ₂) (β : Hom ξ₂ ξ₃) (γ : Hom ξ₃ ξ₄) :
    compHom (compHom α β) γ = compHom α (compHom β γ) := sorry

/-- The category of represented constant-group torsors with an equivariant map to an algebraic space. -/
def category (ρ : G →* Aut X) : Cat.{u + 1, u + 1} :=
  ⟨ObjData ρ, {
    Hom := fun ξ ξ' ↦ Hom ξ ξ'
    id := idHom
    comp := compHom
    id_comp := idHom_comp
    comp_id := compHom_id
    assoc := assocHom
  }⟩

/-- The carrier of the category of represented constant-group torsors with an equivariant map. -/
abbrev Obj (ρ : G →* Aut X) : Type (u + 1) := category ρ

/-- Assemble an object of `[[X/G_S]]` from a `G_S`-torsor and an equivariant map. -/
def ofTorsor (ρ : G →* Aut X) {U : Over S}
    (P : Sheaf.Torsor ((restrictGrp U).obj (GroupScheme.representableGroup .fppf (ConstantGroup.baseChange S (GrpCat.of G)))))
    (φ : P.carrier ⟶ (restrict U).obj (toSmallSheaf X)) (h : IsEquivariant ρ φ) :
    Obj ρ where
  U := U
  P := P
  φ := φ
  equivariant := h

/-- The constructor of `BaseChange.Obj` stores the supplied data. -/
theorem ofTorsor_spec (ρ : G →* Aut X) {U : Over S}
    (P : Sheaf.Torsor ((restrictGrp U).obj (GroupScheme.representableGroup .fppf (ConstantGroup.baseChange S (GrpCat.of G)))))
    (φ : P.carrier ⟶ (restrict U).obj (toSmallSheaf X)) (h : IsEquivariant ρ φ) :
    (ofTorsor ρ P φ h).U = U ∧ (ofTorsor ρ P φ h).P = P ∧
      (ofTorsor ρ P φ h).φ = φ ∧ (ofTorsor ρ P φ h).equivariant = h := ⟨rfl, rfl, rfl, rfl⟩

/-- Assemble a morphism of `[[X/G_S]]`. -/
def ofIso {ρ : G →* Aut X} {ξ ξ' : Obj ρ} (f : ξ.U ⟶ ξ'.U)
    (g : ξ.P.carrier ≅ (inverseImage f).obj ξ'.P.carrier)
    (h : IsEquivariantIso f g) (w : ξ.φ = triangleMap f g) :
    Hom ξ ξ' where
  f := f
  g := g
  equivariant := h
  comm := w

/-- Identity morphisms are sent to identity morphisms. -/
theorem forget_map_id {ρ : G →* Aut X} (ξ : Obj ρ) : (idHom ξ).f = 𝟙 ξ.U := rfl

/-- Composition is preserved on underlying scheme maps. -/
theorem forget_map_comp {ρ : G →* Aut X} {ξ ξ' ξ'' : Obj ρ}
    (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (compHom α β).f = α.f ≫ β.f := rfl

/-- The forgetful functor `[[X/G_S]] ⟶ (Sch/S)_fppf`. -/
def forget (ρ : G →* Aut X) : Obj ρ ⥤ Over S where
  obj ξ := ξ.U
  map α := α.f
  map_id := forget_map_id
  map_comp := forget_map_comp

/-- The forgetful functor sends `(U, P, φ)` to `U`. -/
theorem forget_obj {ρ : G →* Aut X} (ξ : Obj ρ) : (forget ρ).obj ξ = ξ.U := rfl

/-- The forgetful functor sends a morphism `(f, g)` to `f`. -/
theorem forget_map {ρ : G →* Aut X} {ξ ξ' : Obj ρ} (α : Hom ξ ξ') :
    (forget ρ).map α = α.f := rfl

/-- The forgetful functor `[[X/G_S]] ⟶ (Sch/S)_fppf` is a stack in groupoids. -/
instance instIsStackInGroupoids (ρ : G →* Aut X) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (forget ρ) := sorry

/-- The stack in groupoids `[[X/G_S]]` over `(Sch/S)_fppf`. -/
def stack (ρ : G →* Aut X) : StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjection (Scheme.fppfTopology.over S) (forget ρ)

/-- The projection of `stack` is the forgetful functor to `(Sch/S)_fppf`. -/
theorem stack_p (ρ : G →* Aut X) : (stack ρ).p = forget ρ := rfl

/-- The objectwise identification of `underline(G)` with the functor of points of
`G_S` after restriction to `(Sch/U)_fppf`. -/
def groupSheafComponentIso (U : Over S) (V : (Over U.left)ᵒᵖ) :
    (constantGroupSheaf U.left G).obj.obj V ≅
      ((restrictGrp U).obj (GroupScheme.representableGroup .fppf (ConstantGroup.baseChange S (GrpCat.of G)))).obj.obj V :=
  (ConstantGroup.baseChangeComponentIso S (GrpCat.of G)
    (op ((Over.map U.hom).obj V.unop))).symm

/-- Naturality of `groupSheafComponentIso`. -/
theorem groupSheafComponentIso_naturality (U : Over S)
    {V W : (Over U.left)ᵒᵖ} (f : V ⟶ W) :
    (constantGroupSheaf U.left G).obj.map f ≫
        (groupSheafComponentIso U W).hom =
      (groupSheafComponentIso U V).hom ≫
        ((restrictGrp U).obj (GroupScheme.representableGroup .fppf (ConstantGroup.baseChange S (GrpCat.of G)))).obj.map f := sorry

/-- The presheaf identification of `underline(G)` with the restriction of the
functor of points of `G_S`. -/
def groupPresheafIso (U : Over S) :
    (constantGroupSheaf U.left G).obj ≅
      ((restrictGrp U).obj (GroupScheme.representableGroup .fppf (ConstantGroup.baseChange S (GrpCat.of G)))).obj :=
  NatIso.ofComponents (groupSheafComponentIso U)
    (groupSheafComponentIso_naturality U)

/-- The sheaf of groups `underline(G)` on `(Sch/U)_fppf` is isomorphic to the
restriction of the functor of points of `G_S`. -/
def groupSheafIso (U : Over S) :
    constantGroupSheaf U.left G ≅
      (restrictGrp U).obj (GroupScheme.representableGroup .fppf (ConstantGroup.baseChange S (GrpCat.of G))) where
  hom := Sheaf.homEquiv.symm (groupPresheafIso U).hom
  inv := Sheaf.homEquiv.symm (groupPresheafIso U).inv
  hom_inv_id := Sheaf.hom_ext (groupPresheafIso U).hom_inv_id
  inv_hom_id := Sheaf.hom_ext (groupPresheafIso U).inv_hom_id

/-- The canonical transport of an abstract-group equivariant map is equivariant for
represented constant sections. -/
private theorem functorObj_equivariant (ρ : G →* Aut X) (ξ : AbstractGroup.Obj ρ) :
    IsEquivariant ρ (P := ξ.P.transport (groupSheafIso ξ.U)) ξ.φ := sorry

/-- Send a constant-group torsor with an equivariant map to its represented-group presentation. -/
def functorObj (ρ : G →* Aut X) (ξ : AbstractGroup.Obj ρ) : Obj ρ where
  U := ξ.U
  P := ξ.P.transport (groupSheafIso ξ.U)
  φ := ξ.φ
  equivariant := by exact functorObj_equivariant ρ ξ

private theorem functorMap_laws {ρ : G →* Aut X} {ξ ξ' : AbstractGroup.Obj ρ}
    (α : AbstractGroup.Hom ξ ξ') :
    IsEquivariantIso (P := (functorObj ρ ξ).P) (P' := (functorObj ρ ξ').P) α.f α.g ∧
      (functorObj ρ ξ).φ = triangleMap (ξ := functorObj ρ ξ) (ξ' := functorObj ρ ξ')
        α.f α.g := sorry

/-- The comparison preserves the scheme map and underlying torsor isomorphism. -/
def functorMap {ρ : G →* Aut X} {ξ ξ' : AbstractGroup.Obj ρ}
    (α : AbstractGroup.Hom ξ ξ') : Hom (functorObj ρ ξ) (functorObj ρ ξ') where
  f := α.f
  g := α.g
  equivariant := by exact (functorMap_laws α).1
  comm := by exact (functorMap_laws α).2

private theorem functor_laws (ρ : G →* Aut X) :
    (∀ ξ : AbstractGroup.Obj ρ, functorMap (AbstractGroup.idHom ξ) = idHom (functorObj ρ ξ)) ∧
    (∀ {ξ ξ' ξ'' : AbstractGroup.Obj ρ} (α : AbstractGroup.Hom ξ ξ')
      (β : AbstractGroup.Hom ξ' ξ''),
      functorMap (AbstractGroup.compHom α β) = compHom (functorMap α) (functorMap β)) := sorry

/-- The canonical comparison from constant-group torsors to represented-group torsors. -/
def functor (ρ : G →* Aut X) : AbstractGroup.Obj ρ ⥤ Obj ρ where
  obj ξ := functorObj ρ ξ
  map α := functorMap α
  map_id := by exact (functor_laws ρ).1
  map_comp := by exact (functor_laws ρ).2

/-- The canonical comparison preserves the projection to the scheme base. -/
theorem basedFunctor_w (ρ : G →* Aut X) :
    functor ρ ⋙ (stack ρ).p = (AbstractGroup.stack ρ).p := rfl

/-- The canonical comparison as a functor over the scheme base. -/
def basedFunctor (ρ : G →* Aut X) :
    (AbstractGroup.stack ρ).toBasedCategory ⥤ᵇ (stack ρ).toBasedCategory where
  toFunctor := functor ρ
  w := basedFunctor_w ρ

private theorem inverseFunctorObj_equivariant (ρ : G →* Aut X) (ξ : Obj ρ) :
    AbstractGroup.IsEquivariant ρ (P := ξ.P.transport (groupSheafIso ξ.U).symm) ξ.φ := sorry

/-- Recover the abstract-group presentation by transport through the inverse representing isomorphism. -/
def inverseFunctorObj (ρ : G →* Aut X) (ξ : Obj ρ) : AbstractGroup.Obj ρ where
  U := ξ.U
  P := ξ.P.transport (groupSheafIso ξ.U).symm
  φ := ξ.φ
  equivariant := by exact inverseFunctorObj_equivariant ρ ξ

private theorem inverseFunctorMap_laws {ρ : G →* Aut X} {ξ ξ' : Obj ρ}
    (α : Hom ξ ξ') :
    AbstractGroup.IsEquivariantIso (P := (inverseFunctorObj ρ ξ).P)
      (P' := (inverseFunctorObj ρ ξ').P) α.f α.g ∧
    (inverseFunctorObj ρ ξ).φ = AbstractGroup.triangleMap
      (ξ := inverseFunctorObj ρ ξ) (ξ' := inverseFunctorObj ρ ξ') α.f α.g := sorry

/-- Reverse comparison preserves the scheme map and underlying torsor isomorphism. -/
def inverseFunctorMap {ρ : G →* Aut X} {ξ ξ' : Obj ρ}
    (α : Hom ξ ξ') : AbstractGroup.Hom (inverseFunctorObj ρ ξ) (inverseFunctorObj ρ ξ') where
  f := α.f
  g := α.g
  equivariant := by exact (inverseFunctorMap_laws α).1
  comm := by exact (inverseFunctorMap_laws α).2

private theorem inverseFunctor_laws (ρ : G →* Aut X) :
    (∀ ξ : Obj ρ, inverseFunctorMap (idHom ξ) = AbstractGroup.idHom (inverseFunctorObj ρ ξ)) ∧
    (∀ {ξ ξ' ξ'' : Obj ρ} (α : Hom ξ ξ') (β : Hom ξ' ξ''),
      inverseFunctorMap (compHom α β) =
        AbstractGroup.compHom (inverseFunctorMap α) (inverseFunctorMap β)) := sorry

/-- The inverse comparison functor obtained from reverse group-sheaf transport. -/
def inverseFunctor (ρ : G →* Aut X) : Obj ρ ⥤ AbstractGroup.Obj ρ where
  obj ξ := inverseFunctorObj ρ ξ
  map α := inverseFunctorMap α
  map_id := by exact (inverseFunctor_laws ρ).1
  map_comp := by exact (inverseFunctor_laws ρ).2

/-- The reverse comparison as a functor over the scheme base. -/
def inverseBasedFunctor (ρ : G →* Aut X) :
    (stack ρ).toBasedCategory ⥤ᵇ (AbstractGroup.stack ρ).toBasedCategory where
  toFunctor := inverseFunctor ρ
  w := rfl

private def unitComponentLaws (ρ : G →* Aut X) : Prop :=
  ∀ ξ : AbstractGroup.Obj ρ,
    (AbstractGroup.IsEquivariantIso (P := (ξ).P) (P' := (inverseFunctorObj ρ (functorObj ρ ξ)).P) (𝟙 ξ.U)
      ((inverseImageId ξ.U).symm.app ξ.P.carrier) ∧
      (ξ).φ = AbstractGroup.triangleMap (ξ := ξ) (ξ' := inverseFunctorObj ρ (functorObj ρ ξ)) (𝟙 ξ.U)
        ((inverseImageId ξ.U).symm.app ξ.P.carrier)) ∧
    (AbstractGroup.IsEquivariantIso (P := (inverseFunctorObj ρ (functorObj ρ ξ)).P) (P' := (ξ).P) (𝟙 ξ.U)
      ((inverseImageId ξ.U).symm.app ξ.P.carrier) ∧
      (inverseFunctorObj ρ (functorObj ρ ξ)).φ = AbstractGroup.triangleMap (ξ := inverseFunctorObj ρ (functorObj ρ ξ)) (ξ' := ξ) (𝟙 ξ.U)
        ((inverseImageId ξ.U).symm.app ξ.P.carrier))

private def unitHom (ρ : G →* Aut X) (h : unitComponentLaws ρ) (ξ : AbstractGroup.Obj ρ) :
    AbstractGroup.Hom (ξ) (inverseFunctorObj ρ (functorObj ρ ξ)) where
  f := 𝟙 ξ.U
  g := (inverseImageId ξ.U).symm.app ξ.P.carrier
  equivariant := (h ξ).1.1
  comm := (h ξ).1.2

private def unitInv (ρ : G →* Aut X) (h : unitComponentLaws ρ) (ξ : AbstractGroup.Obj ρ) :
    AbstractGroup.Hom (inverseFunctorObj ρ (functorObj ρ ξ)) (ξ) where
  f := 𝟙 ξ.U
  g := (inverseImageId ξ.U).symm.app ξ.P.carrier
  equivariant := (h ξ).2.1
  comm := (h ξ).2.2

private theorem unitIso_laws (ρ : G →* Aut X) :
    unitComponentLaws ρ ∧ ∀ h : unitComponentLaws ρ,
      (∀ ξ : AbstractGroup.Obj ρ,
        AbstractGroup.compHom (unitHom ρ h ξ) (unitInv ρ h ξ) = AbstractGroup.idHom (ξ)) ∧
      (∀ ξ : AbstractGroup.Obj ρ,
        AbstractGroup.compHom (unitInv ρ h ξ) (unitHom ρ h ξ) = AbstractGroup.idHom (inverseFunctorObj ρ (functorObj ρ ξ))) ∧
      (∀ {ξ ξ' : AbstractGroup.Obj ρ} (α : AbstractGroup.Hom ξ ξ'),
        (BasedFunctor.id (AbstractGroup.stack ρ).toBasedCategory).map α ≫ unitHom ρ h ξ' = unitHom ρ h ξ ≫ (BasedFunctor.comp (basedFunctor ρ) (inverseBasedFunctor ρ)).map α) ∧
      (∀ ξ : AbstractGroup.Obj ρ,
        (AbstractGroup.stack ρ).p.IsHomLift (𝟙 ξ.U) (unitHom ρ h ξ)) := sorry

/-- The unit of the torsor comparison has identity underlying sheaf maps and lies over identities. -/
def unitIso (ρ : G →* Aut X) :
    BasedFunctor.id (AbstractGroup.stack ρ).toBasedCategory ≅ BasedFunctor.comp (basedFunctor ρ) (inverseBasedFunctor ρ) :=
  BasedNatIso.ofComponents
    (fun ξ ↦ {
      hom := {
        f := 𝟙 ξ.U
        g := (inverseImageId ξ.U).symm.app ξ.P.carrier
        equivariant := by exact ((unitIso_laws ρ).1 ξ).1.1
        comm := by exact ((unitIso_laws ρ).1 ξ).1.2
      }
      inv := {
        f := 𝟙 ξ.U
        g := (inverseImageId ξ.U).symm.app ξ.P.carrier
        equivariant := by exact ((unitIso_laws ρ).1 ξ).2.1
        comm := by exact ((unitIso_laws ρ).1 ξ).2.2
      }
      hom_inv_id := by exact ((unitIso_laws ρ).2 (unitIso_laws ρ).1).1 ξ
      inv_hom_id := by exact ((unitIso_laws ρ).2 (unitIso_laws ρ).1).2.1 ξ
    })
    (by exact ((unitIso_laws ρ).2 (unitIso_laws ρ).1).2.2.1)
    (by exact ((unitIso_laws ρ).2 (unitIso_laws ρ).1).2.2.2)

private def counitComponentLaws (ρ : G →* Aut X) : Prop :=
  ∀ ξ : Obj ρ,
    (IsEquivariantIso (P := (functorObj ρ (inverseFunctorObj ρ ξ)).P) (P' := (ξ).P) (𝟙 ξ.U)
      ((inverseImageId ξ.U).symm.app ξ.P.carrier) ∧
      (functorObj ρ (inverseFunctorObj ρ ξ)).φ = triangleMap (ξ := functorObj ρ (inverseFunctorObj ρ ξ)) (ξ' := ξ) (𝟙 ξ.U)
        ((inverseImageId ξ.U).symm.app ξ.P.carrier)) ∧
    (IsEquivariantIso (P := (ξ).P) (P' := (functorObj ρ (inverseFunctorObj ρ ξ)).P) (𝟙 ξ.U)
      ((inverseImageId ξ.U).symm.app ξ.P.carrier) ∧
      (ξ).φ = triangleMap (ξ := ξ) (ξ' := functorObj ρ (inverseFunctorObj ρ ξ)) (𝟙 ξ.U)
        ((inverseImageId ξ.U).symm.app ξ.P.carrier))

private def counitHom (ρ : G →* Aut X) (h : counitComponentLaws ρ) (ξ : Obj ρ) :
    Hom (functorObj ρ (inverseFunctorObj ρ ξ)) (ξ) where
  f := 𝟙 ξ.U
  g := (inverseImageId ξ.U).symm.app ξ.P.carrier
  equivariant := (h ξ).1.1
  comm := (h ξ).1.2

private def counitInv (ρ : G →* Aut X) (h : counitComponentLaws ρ) (ξ : Obj ρ) :
    Hom (ξ) (functorObj ρ (inverseFunctorObj ρ ξ)) where
  f := 𝟙 ξ.U
  g := (inverseImageId ξ.U).symm.app ξ.P.carrier
  equivariant := (h ξ).2.1
  comm := (h ξ).2.2

private theorem counitIso_laws (ρ : G →* Aut X) :
    counitComponentLaws ρ ∧ ∀ h : counitComponentLaws ρ,
      (∀ ξ : Obj ρ,
        compHom (counitHom ρ h ξ) (counitInv ρ h ξ) = idHom (functorObj ρ (inverseFunctorObj ρ ξ))) ∧
      (∀ ξ : Obj ρ,
        compHom (counitInv ρ h ξ) (counitHom ρ h ξ) = idHom (ξ)) ∧
      (∀ {ξ ξ' : Obj ρ} (α : Hom ξ ξ'),
        (BasedFunctor.comp (inverseBasedFunctor ρ) (basedFunctor ρ)).map α ≫ counitHom ρ h ξ' = counitHom ρ h ξ ≫ (BasedFunctor.id (stack ρ).toBasedCategory).map α) ∧
      (∀ ξ : Obj ρ,
        (stack ρ).p.IsHomLift (𝟙 ξ.U) (counitHom ρ h ξ)) := sorry

/-- The counit of the torsor comparison has identity underlying sheaf maps and lies over identities. -/
def counitIso (ρ : G →* Aut X) :
    BasedFunctor.comp (inverseBasedFunctor ρ) (basedFunctor ρ) ≅ BasedFunctor.id (stack ρ).toBasedCategory :=
  BasedNatIso.ofComponents
    (fun ξ ↦ {
      hom := {
        f := 𝟙 ξ.U
        g := (inverseImageId ξ.U).symm.app ξ.P.carrier
        equivariant := by exact ((counitIso_laws ρ).1 ξ).1.1
        comm := by exact ((counitIso_laws ρ).1 ξ).1.2
      }
      inv := {
        f := 𝟙 ξ.U
        g := (inverseImageId ξ.U).symm.app ξ.P.carrier
        equivariant := by exact ((counitIso_laws ρ).1 ξ).2.1
        comm := by exact ((counitIso_laws ρ).1 ξ).2.2
      }
      hom_inv_id := by exact ((counitIso_laws ρ).2 (counitIso_laws ρ).1).1 ξ
      inv_hom_id := by exact ((counitIso_laws ρ).2 (counitIso_laws ρ).1).2.1 ξ
    })
    (by exact ((counitIso_laws ρ).2 (counitIso_laws ρ).1).2.2.1)
    (by exact ((counitIso_laws ρ).2 (counitIso_laws ρ).1).2.2.2)

/-- Explicit inverse comparison and identity-carrier unit and counit over the base. -/
def quasiInverse (ρ : G →* Aut X) : BasedFunctor.QuasiInverse (basedFunctor ρ) where
  inverse := inverseBasedFunctor ρ
  unitIso := unitIso ρ
  counitIso := counitIso ρ

/-- The canonical comparison morphism of quotient stacks. -/
def hom (ρ : G →* Aut X) : AbstractGroup.stack ρ ⟶ stack ρ :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor (basedFunctor ρ))

/-- The canonical quotient comparison is an equivalence over the scheme base. -/
theorem hom_isEquivalence (ρ : G →* Aut X) :
    StackOver.Groupoids.Hom.IsEquivalence (hom ρ) :=
  (quasiInverse ρ).isEquivalence

/-- The quotient by an abstract group is equivalent over the base to its represented
constant-group-scheme presentation. -/
def equivalent_baseChange (ρ : G →* Aut X) : AbstractGroup.stack ρ ≌ stack ρ :=
  ObjectProperty.FullSubbicategory.equivalenceOfAmbient
    (ObjectProperty.FullSubbicategory.equivalenceOfAmbient (quasiInverse ρ).toEquivalence)

/-- The forward morphism of the quotient equivalence is the canonical torsor comparison. -/
theorem equivalent_baseChange_hom (ρ : G →* Aut X) :
    (equivalent_baseChange ρ).hom = hom ρ := sorry

/-- The forward morphism of the quotient equivalence is an equivalence over the base. -/
theorem equivalent_baseChange_isEquivalence (ρ : G →* Aut X) :
    StackOver.Groupoids.Hom.IsEquivalence (equivalent_baseChange ρ).hom := by
  rw [equivalent_baseChange_hom]
  exact hom_isEquivalence ρ

end AlgebraicGeometry.QuotientStack.BaseChange
