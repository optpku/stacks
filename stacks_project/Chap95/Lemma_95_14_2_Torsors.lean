module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Basic
public import stacks_project.Chap95.Lemma_95_14_2_Restriction

/-!
# The fibered category of torsors under a sheaf of groups

Objects of `𝒢`-Torsors are pairs `(U, ℱ)` with `ℱ` a `𝒢|_U`-torsor on
`(Sch/U)_fppf`. Morphisms are pairs `(f, α)` with `α : f⁻¹ℋ ≅ ℱ` an
isomorphism of `𝒢|_U`-torsors. The forgetful functor sends `(U, ℱ)` to `U`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.SheafTorsors

variable {S : Scheme.{u}}

/-- An object of `𝒢`-Torsors: a scheme over `S` together with a torsor under
the restricted sheaf of groups. -/
structure Obj (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}) where
  /-- The underlying scheme over `S`. -/
  U : Over S
  /-- The `𝒢|_U`-torsor. -/
  P : Sheaf.Torsor ((restrictGrp U).obj 𝒢)

/-- Assemble an object of `𝒢`-Torsors from a scheme over `S` and a `𝒢|_U`-torsor. -/
def ofTorsor {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} (U : Over S)
    (P : Sheaf.Torsor ((restrictGrp U).obj 𝒢)) : Obj 𝒢 where
  U := U
  P := P

/-- The constructor of `Obj` stores the supplied scheme. -/
theorem ofTorsor_U {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} (U : Over S)
    (P : Sheaf.Torsor ((restrictGrp U).obj 𝒢)) : (ofTorsor U P).U = U := sorry

/-- The constructor of `Obj` stores the supplied torsor. -/
theorem ofTorsor_P {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} (U : Over S)
    (P : Sheaf.Torsor ((restrictGrp U).obj 𝒢)) : (ofTorsor U P).P = P := sorry

/-- A carrier isomorphism over `f` is equivariant if it intertwines the
`𝒢|_U`-actions. -/
def IsEquivariant {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {ξ ξ' : Obj 𝒢} (f : ξ.U ⟶ ξ'.U)
    (g : (inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier) : Prop :=
  ∀ (V : Over ξ.U.left)
    (γ : ((restrictGrp ξ.U).obj 𝒢).obj.obj (op V))
    (x : ((inverseImage f).obj ξ'.P.carrier).obj.obj (op V)),
    g.hom.hom.app (op V) (((inverseImageTorsor f ξ'.P).mulAction V).smul γ x) =
      (ξ.P.mulAction V).smul γ (g.hom.hom.app (op V) x)

/-- A morphism of `𝒢`-Torsors: a map of schemes over `S` and an isomorphism
of `𝒢|_U`-torsors `f⁻¹ℋ ≅ ℱ`. -/
structure Hom {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} (ξ ξ' : Obj 𝒢) where
  /-- The underlying morphism of schemes over `S`. -/
  f : ξ.U ⟶ ξ'.U
  /-- The isomorphism `f⁻¹ℋ ≅ ℱ` of `𝒢|_U`-torsors. -/
  iso : TorsorIso (inverseImageTorsor f ξ'.P) ξ.P

/-- The forward comparison of an equivariant carrier isomorphism is a morphism
of torsors. -/
theorem ofCarrierIso_hom_comm {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {ξ ξ' : Obj 𝒢} (f : ξ.U ⟶ ξ'.U)
    (g : (inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier) (h : IsEquivariant f g)
    (V : Over ξ.U.left) (γ : ((restrictGrp ξ.U).obj 𝒢).obj.obj (op V))
    (x : (inverseImageTorsor f ξ'.P).carrier.obj.obj (op V)) :
    g.hom.hom.app (op V) (((inverseImageTorsor f ξ'.P).mulAction V).smul γ x) =
      (ξ.P.mulAction V).smul γ (g.hom.hom.app (op V) x) := sorry

/-- The inverse comparison of an equivariant carrier isomorphism is a morphism
of torsors. -/
theorem ofCarrierIso_inv_comm {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {ξ ξ' : Obj 𝒢} (f : ξ.U ⟶ ξ'.U)
    (g : (inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier) (h : IsEquivariant f g)
    (V : Over ξ.U.left) (γ : ((restrictGrp ξ.U).obj 𝒢).obj.obj (op V))
    (x : ξ.P.carrier.obj.obj (op V)) :
    g.inv.hom.app (op V) ((ξ.P.mulAction V).smul γ x) =
      ((inverseImageTorsor f ξ'.P).mulAction V).smul γ (g.inv.hom.app (op V) x) :=
  sorry

/-- Promote an equivariant carrier isomorphism to an isomorphism of torsors. -/
def ofCarrierIso {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {ξ ξ' : Obj 𝒢}
    (f : ξ.U ⟶ ξ'.U) (g : (inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier)
    (h : IsEquivariant f g) :
    TorsorIso (inverseImageTorsor f ξ'.P) ξ.P :=
  TorsorIso.mk
    { hom := g.hom
      comm := ofCarrierIso_hom_comm f g h }
    { hom := g.inv
      comm := ofCarrierIso_inv_comm f g h }

/-- Assemble a morphism of `𝒢`-Torsors from a scheme map and an equivariant
carrier isomorphism. -/
def ofIso {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {ξ ξ' : Obj 𝒢}
    (f : ξ.U ⟶ ξ'.U) (g : (inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier)
    (h : IsEquivariant f g) : Hom ξ ξ' where
  f := f
  iso := ofCarrierIso f g h

/-- The constructor of `Hom` stores the supplied scheme map. -/
theorem ofIso_f {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {ξ ξ' : Obj 𝒢}
    (f : ξ.U ⟶ ξ'.U) (g : (inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier)
    (h : IsEquivariant f g) : (ofIso f g h).f = f := sorry

/-- The constructor of `Hom` stores the promoted torsor isomorphism. -/
theorem ofIso_iso {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {ξ ξ' : Obj 𝒢}
    (f : ξ.U ⟶ ξ'.U) (g : (inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier)
    (h : IsEquivariant f g) : (ofIso f g h).iso = ofCarrierIso f g h := sorry

/-- Identity morphisms of `𝒢`-Torsors. -/
def idHom {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} (ξ : Obj 𝒢) : Hom ξ ξ where
  f := 𝟙 ξ.U
  iso := inverseImageTorsorId ξ.P

/-- The composite isomorphism of torsors along a composite of scheme maps. -/
def compIso {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {ξ ξ' ξ'' : Obj 𝒢}
    (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    TorsorIso (inverseImageTorsor (α.f ≫ β.f) ξ''.P) ξ.P :=
  TorsorIso.trans (inverseImageTorsorComp α.f β.f ξ''.P)
    (TorsorIso.trans (inverseImageTorsorMap α.f β.iso) α.iso)

/-- Composition of morphisms of `𝒢`-Torsors. -/
def compHom {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {ξ ξ' ξ'' : Obj 𝒢}
    (α : Hom ξ ξ') (β : Hom ξ' ξ'') : Hom ξ ξ'' where
  f := α.f ≫ β.f
  iso := compIso α β

/-- Left identity law for morphisms of `𝒢`-Torsors. -/
theorem idHom_comp {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {ξ ξ' : Obj 𝒢}
    (α : Hom ξ ξ') : compHom (idHom ξ) α = α := sorry

/-- Right identity law for morphisms of `𝒢`-Torsors. -/
theorem compHom_id {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {ξ ξ' : Obj 𝒢}
    (α : Hom ξ ξ') : compHom α (idHom ξ') = α := sorry

/-- Associativity of composition of morphisms of `𝒢`-Torsors. -/
theorem assocHom {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {ξ₁ ξ₂ ξ₃ ξ₄ : Obj 𝒢} (α : Hom ξ₁ ξ₂) (β : Hom ξ₂ ξ₃) (γ : Hom ξ₃ ξ₄) :
    compHom (compHom α β) γ = compHom α (compHom β γ) := sorry

/-- The category of objects of `𝒢`-Torsors. -/
instance instCategory (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}) :
    Category (Obj 𝒢) where
  Hom ξ ξ' := Hom ξ ξ'
  id ξ := idHom ξ
  comp α β := compHom α β
  id_comp := idHom_comp
  comp_id := compHom_id
  assoc := assocHom

/-- The forgetful functor sends identity morphisms to identity morphisms. -/
theorem forget_map_id {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} (ξ : Obj 𝒢) :
    (idHom ξ).f = 𝟙 ξ.U := sorry

/-- The forgetful functor preserves composition. -/
theorem forget_map_comp {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {ξ ξ' ξ'' : Obj 𝒢} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (compHom α β).f = α.f ≫ β.f := sorry

/-- The forgetful functor `𝒢`-Torsors `⟶` `(Sch/S)_fppf`. -/
def forget (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}) : Obj 𝒢 ⥤ Over S where
  obj ξ := ξ.U
  map α := α.f
  map_id := forget_map_id
  map_comp := forget_map_comp

/-- The forgetful functor sends `(U, ℱ)` to `U`. -/
theorem forget_obj {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} (ξ : Obj 𝒢) :
    (forget 𝒢).obj ξ = ξ.U := sorry

/-- The forgetful functor sends a morphism `(f, α)` to `f`. -/
theorem forget_map {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {ξ ξ' : Obj 𝒢} (α : Hom ξ ξ') : (forget 𝒢).map α = α.f := sorry

/-- The underlying carrier isomorphism of a morphism of `𝒢`-Torsors. -/
def Hom.carrierIso {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {ξ ξ' : Obj 𝒢}
    (α : Hom ξ ξ') : (inverseImage α.f).obj ξ'.P.carrier ≅ ξ.P.carrier where
  hom := (TorsorIso.hom α.iso).hom
  inv := (TorsorIso.inv α.iso).hom
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The carrier isomorphism of a morphism of `𝒢`-Torsors is equivariant. -/
theorem iso_iff_carrier {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {ξ ξ' : Obj 𝒢} (α : Hom ξ ξ') : IsEquivariant α.f (Hom.carrierIso α) := sorry

/-- The forgetful functor `𝒢`-Torsors `⟶` `(Sch/S)_fppf` is fibered in groupoids. -/
instance instIsFiberedInGroupoids (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}) :
    Functor.IsFibered.InGroupoids (forget 𝒢) := sorry

end AlgebraicGeometry.SheafTorsors
