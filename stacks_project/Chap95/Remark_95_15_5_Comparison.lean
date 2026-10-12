/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.GroupScheme.RepresentableTorsor
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Equivalence
public import stacks_project.Chap95.Remark_95_15_5_Quotient

/-!
# Comparison of `[[X/G]]` with the quotient by the constant group scheme `G_S`

This module records the sheaf-level stack `[[X/G_S]]` and the identification of
the constant sheaf `underline(G)` with the functor of points of `G_S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace (toSheaf)
open AlgebraicGeometry.QuotientStack.AbstractGroup
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.QuotientStack.BaseChange

/-- The fppf group sheaf represented by the constant group scheme `G_S`. -/
def representableConstantGroup (S : Scheme.{u}) (G : Type u) [Group G] :
    Sheaf (Scheme.fppfTopology.over S) GrpCat.{u} where
  obj := yonedaGrp.obj (ConstantGroup.baseChange S (GrpCat.of G))
  property := GroupScheme.representableGroup_isSheaf .fppf
    (ConstantGroup.baseChange S (GrpCat.of G))

/-- The underlying presheaf of `representableConstantGroup` is group-valued Yoneda
of `G_S`. -/
theorem representableConstantGroup_obj (S : Scheme.{u}) (G : Type u) [Group G] :
    (representableConstantGroup S G).obj =
      yonedaGrp.obj (ConstantGroup.baseChange S (GrpCat.of G)) := sorry

/-- The constant sheaf `underline(G)` is represented by `G_S` on `(Sch/S)_fppf`. -/
theorem constantSheaf_represented (S : Scheme.{u}) (G : GrpCat.{u}) :
    IsIsomorphic (constantGroupSheaf S G).obj
      (yonedaGrp.obj (ConstantGroup.baseChange S G)) := sorry

variable {S : Scheme.{u}} {G : Type u} [Group G] {X : AlgebraicSpace S}

/-- The constant `G_S`-valued map associated to an abstract group element. -/
def constSection (U : Over S) (V : Over U.left) (g : G) :
    ((restrictGrp U).obj (representableConstantGroup S G)).obj.obj (op V) :=
  (ConstantGroup.baseChangeHomEquiv S (GrpCat.of G) ((Over.map U.hom).obj V)).symm
    (LocallyConstant.const ((Over.map U.hom).obj V).left g)

/-- The action of a group element on a section of a `G_S`-torsor. -/
def torsorAct {U : Over S}
    (P : Sheaf.Torsor ((restrictGrp U).obj (representableConstantGroup S G)))
    (V : (Over U.left)ᵒᵖ) (g : G) (x : P.carrier.obj.obj V) :
    P.carrier.obj.obj V :=
  (P.mulAction V.unop).toSMul.smul (constSection U V.unop g) x

/-- Naturality of translation by a constant section of `G_S`. -/
theorem torsorAut_naturality {U : Over S}
    (P : Sheaf.Torsor ((restrictGrp U).obj (representableConstantGroup S G))) (g : G)
    {V W : (Over U.left)ᵒᵖ} (f : V ⟶ W) :
    P.carrier.obj.map f ≫ TypeCat.ofHom (torsorAct P W g) =
      TypeCat.ofHom (torsorAct P V g) ≫ P.carrier.obj.map f := sorry

/-- Translation by `g` on the underlying sheaf of a `G_S`-torsor. -/
def torsorAut {U : Over S}
    (P : Sheaf.Torsor ((restrictGrp U).obj (representableConstantGroup S G))) (g : G) :
    P.carrier ⟶ P.carrier :=
  Sheaf.homEquiv.symm
    { app := fun V ↦ TypeCat.ofHom (torsorAct P V g)
      naturality := fun _ _ f ↦ torsorAut_naturality P g f }

/-- A sheaf map `φ : P ⟶ X|_U` is `G`-equivariant for the action `ρ`. -/
def IsEquivariant (ρ : G →* Aut X) {U : Over S}
    {P : Sheaf.Torsor ((restrictGrp U).obj (representableConstantGroup S G))}
    (φ : P.carrier ⟶ (restrict U).obj (toSheaf X)) : Prop :=
  ∀ g : G, torsorAut P g ≫ φ = φ ≫ (restrict U).map (autSheaf ρ g)

/-- An object of `[[X/G_S]]`: a scheme `U` over `S`, a `G_S`-torsor on
`(Sch/U)_fppf`, and a `G`-equivariant map to `X`. -/
structure Obj (ρ : G →* Aut X) where
  /-- The underlying scheme over `S`. -/
  U : Over S
  /-- The `G_S`-torsor on `(Sch/U)_fppf`. -/
  P : Sheaf.Torsor ((restrictGrp U).obj (representableConstantGroup S G))
  /-- The `G`-equivariant sheaf map `P ⟶ X|_U`. -/
  φ : P.carrier ⟶ (restrict U).obj (toSheaf X)
  /-- The map `φ` intertwines the `G`-actions. -/
  equivariant : IsEquivariant ρ φ

/-- Assemble an object of `[[X/G_S]]` from a `G_S`-torsor and an equivariant map. -/
def ofTorsor (ρ : G →* Aut X) {U : Over S}
    (P : Sheaf.Torsor ((restrictGrp U).obj (representableConstantGroup S G)))
    (φ : P.carrier ⟶ (restrict U).obj (toSheaf X)) (h : IsEquivariant ρ φ) :
    Obj ρ where
  U := U
  P := P
  φ := φ
  equivariant := h

/-- The constructor of `BaseChange.Obj` stores the supplied data. -/
theorem ofTorsor_spec (ρ : G →* Aut X) {U : Over S}
    (P : Sheaf.Torsor ((restrictGrp U).obj (representableConstantGroup S G)))
    (φ : P.carrier ⟶ (restrict U).obj (toSheaf X)) (h : IsEquivariant ρ φ) :
    (ofTorsor ρ P φ h).U = U ∧ (ofTorsor ρ P φ h).P = P ∧
      (ofTorsor ρ P φ h).φ = φ ∧ (ofTorsor ρ P φ h).equivariant = h := sorry

/-- A morphism of `G_S`-torsors over a map of schemes is `G`-equivariant. -/
def IsEquivariantIso {U U' : Over S}
    {P : Sheaf.Torsor ((restrictGrp U).obj (representableConstantGroup S G))}
    {P' : Sheaf.Torsor ((restrictGrp U').obj (representableConstantGroup S G))}
    (f : U ⟶ U') (g : P.carrier ≅ (inverseImage f).obj P'.carrier) : Prop :=
  ∀ γ : G, torsorAut P γ ≫ g.hom = g.hom ≫ (inverseImage f).map (torsorAut P' γ)

/-- The comparison `φ' ∘ g` after transporting `φ'` along `f`. -/
def triangleMap {ρ : G →* Aut X} {ξ ξ' : Obj ρ} (f : ξ.U ⟶ ξ'.U)
    (g : ξ.P.carrier ≅ (inverseImage f).obj ξ'.P.carrier) :
    ξ.P.carrier ⟶ (restrict ξ.U).obj (toSheaf X) :=
  g.hom ≫ (inverseImage f).map ξ'.φ ≫ (restrictIso f).hom.app (toSheaf X)

/-- A morphism of `[[X/G_S]]`. -/
structure Hom {ρ : G →* Aut X} (ξ ξ' : Obj ρ) where
  /-- The underlying morphism of schemes over `S`. -/
  f : ξ.U ⟶ ξ'.U
  /-- The `G`-equivariant isomorphism `P ≅ f⁻¹ P'`. -/
  g : ξ.P.carrier ≅ (inverseImage f).obj ξ'.P.carrier
  /-- The isomorphism `g` is `G`-equivariant. -/
  equivariant : IsEquivariantIso f g
  /-- The triangle identity `φ = φ' ∘ g`. -/
  comm : ξ.φ = triangleMap f g

/-- Assemble a morphism of `[[X/G_S]]`. -/
def ofIso {ρ : G →* Aut X} {ξ ξ' : Obj ρ} (f : ξ.U ⟶ ξ'.U)
    (g : ξ.P.carrier ≅ (inverseImage f).obj ξ'.P.carrier)
    (h : IsEquivariantIso f g) (w : ξ.φ = triangleMap f g) :
    Hom ξ ξ' where
  f := f
  g := g
  equivariant := h
  comm := w

/-- The identity comparison of `G_S`-torsors is `G`-equivariant. -/
theorem id_equivariant {ρ : G →* Aut X} (ξ : Obj ρ) :
    IsEquivariantIso (𝟙 ξ.U) ((inverseImageId ξ.U).symm.app ξ.P.carrier) := sorry

/-- The identity comparison satisfies the triangle identity. -/
theorem id_comm {ρ : G →* Aut X} (ξ : Obj ρ) :
    ξ.φ = triangleMap (𝟙 ξ.U) ((inverseImageId ξ.U).symm.app ξ.P.carrier) := sorry

/-- Identity morphisms of `[[X/G_S]]`. -/
def idHom {ρ : G →* Aut X} (ξ : Obj ρ) : Hom ξ ξ where
  f := 𝟙 ξ.U
  g := (inverseImageId ξ.U).symm.app ξ.P.carrier
  equivariant := id_equivariant ξ
  comm := id_comm ξ

/-- The composite isomorphism of `G_S`-torsors. -/
def compIso {ρ : G →* Aut X} {ξ ξ' ξ'' : Obj ρ} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.P.carrier ≅ (inverseImage (α.f ≫ β.f)).obj ξ''.P.carrier :=
  α.g ≪≫ (inverseImage α.f).mapIso β.g ≪≫
    (inverseImageComp α.f β.f).app ξ''.P.carrier

/-- The composite isomorphism of `G_S`-torsors is `G`-equivariant. -/
theorem comp_equivariant {ρ : G →* Aut X} {ξ ξ' ξ'' : Obj ρ}
    (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    IsEquivariantIso (α.f ≫ β.f) (compIso α β) := sorry

/-- The composite morphism satisfies the triangle identity. -/
theorem comp_comm {ρ : G →* Aut X} {ξ ξ' ξ'' : Obj ρ}
    (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.φ = triangleMap (α.f ≫ β.f) (compIso α β) := sorry

/-- Composition of morphisms of `[[X/G_S]]`. -/
def compHom {ρ : G →* Aut X} {ξ ξ' ξ'' : Obj ρ} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    Hom ξ ξ'' where
  f := α.f ≫ β.f
  g := compIso α β
  equivariant := comp_equivariant α β
  comm := comp_comm α β

/-- Left identity law for morphisms of `[[X/G_S]]`. -/
theorem idHom_comp {ρ : G →* Aut X} {ξ ξ' : Obj ρ} (α : Hom ξ ξ') :
    compHom (idHom ξ) α = α := sorry

/-- Right identity law for morphisms of `[[X/G_S]]`. -/
theorem compHom_id {ρ : G →* Aut X} {ξ ξ' : Obj ρ} (α : Hom ξ ξ') :
    compHom α (idHom ξ') = α := sorry

/-- Associativity of composition of morphisms of `[[X/G_S]]`. -/
theorem assocHom {ρ : G →* Aut X} {ξ₁ ξ₂ ξ₃ ξ₄ : Obj ρ}
    (α : Hom ξ₁ ξ₂) (β : Hom ξ₂ ξ₃) (γ : Hom ξ₃ ξ₄) :
    compHom (compHom α β) γ = compHom α (compHom β γ) := sorry

/-- The category of objects of `[[X/G_S]]`. -/
instance instCategoryObj (ρ : G →* Aut X) : Category (Obj ρ) where
  Hom ξ ξ' := Hom ξ ξ'
  id ξ := idHom ξ
  comp α β := compHom α β
  id_comp := idHom_comp
  comp_id := compHom_id
  assoc := assocHom

/-- Identity morphisms are sent to identity morphisms. -/
theorem forget_map_id {ρ : G →* Aut X} (ξ : Obj ρ) : (idHom ξ).f = 𝟙 ξ.U := sorry

/-- Composition is preserved on underlying scheme maps. -/
theorem forget_map_comp {ρ : G →* Aut X} {ξ ξ' ξ'' : Obj ρ}
    (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (compHom α β).f = α.f ≫ β.f := sorry

/-- The forgetful functor `[[X/G_S]] ⟶ (Sch/S)_fppf`. -/
def forget (ρ : G →* Aut X) : Obj ρ ⥤ Over S where
  obj ξ := ξ.U
  map α := α.f
  map_id := forget_map_id
  map_comp := forget_map_comp

/-- The forgetful functor sends `(U, P, φ)` to `U`. -/
theorem forget_obj {ρ : G →* Aut X} (ξ : Obj ρ) : (forget ρ).obj ξ = ξ.U := sorry

/-- The forgetful functor sends a morphism `(f, g)` to `f`. -/
theorem forget_map {ρ : G →* Aut X} {ξ ξ' : Obj ρ} (α : Hom ξ ξ') :
    (forget ρ).map α = α.f := sorry

/-- The forgetful functor `[[X/G_S]] ⟶ (Sch/S)_fppf` is a stack in groupoids. -/
instance instIsStackInGroupoids (ρ : G →* Aut X) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (forget ρ) := sorry

/-- The stack in groupoids `[[X/G_S]]` over `(Sch/S)_fppf`. -/
def stack (ρ : G →* Aut X) : StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjection (Scheme.fppfTopology.over S) (forget ρ)

/-- The projection of `stack` is the forgetful functor to `(Sch/S)_fppf`. -/
theorem stack_p (ρ : G →* Aut X) : (stack ρ).p = forget ρ := sorry

/-- The objectwise identification of `underline(G)` with the functor of points of
`G_S` after restriction to `(Sch/U)_fppf`. -/
def groupSheafComponentIso (U : Over S) (V : (Over U.left)ᵒᵖ) :
    (constantGroupSheaf U.left G).obj.obj V ≅
      ((restrictGrp U).obj (representableConstantGroup S G)).obj.obj V :=
  (ConstantGroup.baseChangeComponentIso S (GrpCat.of G)
    (op ((Over.map U.hom).obj V.unop))).symm

/-- Naturality of `groupSheafComponentIso`. -/
theorem groupSheafComponentIso_naturality (U : Over S)
    {V W : (Over U.left)ᵒᵖ} (f : V ⟶ W) :
    (constantGroupSheaf U.left G).obj.map f ≫
        (groupSheafComponentIso U W).hom =
      (groupSheafComponentIso U V).hom ≫
        ((restrictGrp U).obj (representableConstantGroup S G)).obj.map f := sorry

/-- The presheaf identification of `underline(G)` with the restriction of the
functor of points of `G_S`. -/
def groupPresheafIso (U : Over S) :
    (constantGroupSheaf U.left G).obj ≅
      ((restrictGrp U).obj (representableConstantGroup S G)).obj :=
  NatIso.ofComponents (groupSheafComponentIso U)
    (groupSheafComponentIso_naturality U)

/-- The sheaf of groups `underline(G)` on `(Sch/U)_fppf` is isomorphic to the
restriction of the functor of points of `G_S`. -/
def groupSheafIso (U : Over S) :
    constantGroupSheaf U.left G ≅
      (restrictGrp U).obj (representableConstantGroup S G) where
  hom := Sheaf.homEquiv.symm (groupPresheafIso U).hom
  inv := Sheaf.homEquiv.symm (groupPresheafIso U).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The conjugated action of a `G_S`-section on an `underline(G)`-torsor. -/
def transportTorsorSMul (U : Over S)
    (P : Sheaf.Torsor (constantGroupSheaf U.left G)) (V : Over U.left)
    (g : ((restrictGrp U).obj (representableConstantGroup S G)).obj.obj (op V))
    (x : P.carrier.obj.obj (op V)) : P.carrier.obj.obj (op V) :=
  (P.mulAction V).toSMul.smul ((groupSheafIso U).inv.hom.app (op V) g) x

/-- Transport an `underline(G)`-torsor to a torsor under the restriction of
`G_S`. -/
def transportTorsor (U : Over S)
    (P : Sheaf.Torsor (constantGroupSheaf U.left G)) :
    Sheaf.Torsor ((restrictGrp U).obj (representableConstantGroup S G)) where
  carrier := P.carrier
  mulAction V :=
    { smul := transportTorsorSMul U P V
      one_smul := sorry
      mul_smul := sorry }
  act_naturality := sorry
  isPretransitive := sorry
  isCancelSMul := sorry
  locallyNonempty := P.locallyNonempty

/-- Reinterpret a map out of an `underline(G)`-torsor after transport to `G_S`. -/
def transportTorsor_hom {U : Over S}
    {P : Sheaf.Torsor (constantGroupSheaf U.left G)}
    {F : Sheaf (Scheme.fppfTopology.over U.left) (Type u)}
    (φ : P.carrier ⟶ F) : (transportTorsor U P).carrier ⟶ F := φ

/-- Reinterpret an isomorphism of underlying sheaves after transport to `G_S`. -/
def transportTorsor_iso {U U' : Over S} (f : U ⟶ U')
    {P : Sheaf.Torsor (constantGroupSheaf U.left G)}
    {P' : Sheaf.Torsor (constantGroupSheaf U'.left G)}
    (g : P.carrier ≅ (inverseImage f).obj P'.carrier) :
    (transportTorsor U P).carrier ≅
      (inverseImage f).obj (transportTorsor U' P').carrier := g

/-- Send an object of `[[X/G]]` to the corresponding object of `[[X/G_S]]`. -/
def functorObj (ρ : G →* Aut X) (ξ : AbstractGroup.Obj ρ) : Obj ρ where
  U := ξ.U
  P := transportTorsor ξ.U ξ.P
  φ := transportTorsor_hom ξ.φ
  equivariant := sorry

/-- Send a morphism of `[[X/G]]` to the corresponding morphism of `[[X/G_S]]`. -/
def functorMap {ρ : G →* Aut X} {ξ ξ' : AbstractGroup.Obj ρ}
    (α : AbstractGroup.Hom ξ ξ') : Hom (functorObj ρ ξ) (functorObj ρ ξ') where
  f := α.f
  g := transportTorsor_iso α.f α.g
  equivariant := sorry
  comm := sorry

/-- The comparison functor on objects of `[[X/G]]` and `[[X/G_S]]`. -/
def functor (ρ : G →* Aut X) : AbstractGroup.Obj ρ ⥤ Obj ρ where
  obj ξ := functorObj ρ ξ
  map α := functorMap α
  map_id := sorry
  map_comp := sorry

/-- The comparison functor lies over `(Sch/S)_fppf`. -/
theorem basedFunctor_w (ρ : G →* Aut X) :
    functor ρ ⋙ (stack ρ).p = (AbstractGroup.stack ρ).p := sorry

/-- The based comparison functor `[[X/G]] ⥤ᵇ [[X/G_S]]` over `(Sch/S)_fppf`. -/
def basedFunctor (ρ : G →* Aut X) :
    (AbstractGroup.stack ρ).toBasedCategory ⥤ᵇ (stack ρ).toBasedCategory where
  toFunctor := functor ρ
  w := basedFunctor_w ρ

/-- The comparison morphism of stacks `[[X/G]] ⟶ [[X/G_S]]`. -/
def hom (ρ : G →* Aut X) : AbstractGroup.stack ρ ⟶ stack ρ :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor (basedFunctor ρ))

/-- The comparison morphism of stacks is an equivalence over `(Sch/S)_fppf`. -/
theorem hom_isEquivalence (ρ : G →* Aut X) :
    StackOver.Groupoids.Hom.IsEquivalence (hom ρ) := sorry

/-- The abstract-group quotient stack is equivalent to the `G_S` presentation. -/
noncomputable def equivalent_baseChange (ρ : G →* Aut X) :
    AbstractGroup.stack ρ ≌ stack ρ :=
  StackOver.Groupoids.Hom.asEquivalenceOf (hom_isEquivalence ρ)

/-- The forward morphism of `equivalent_baseChange` is the comparison `hom`. -/
theorem equivalent_baseChange_hom (ρ : G →* Aut X) :
    (equivalent_baseChange ρ).hom = hom ρ := sorry

end AlgebraicGeometry.QuotientStack.BaseChange

