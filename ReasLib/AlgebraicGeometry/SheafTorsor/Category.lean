module

public import ReasLib.AlgebraicGeometry.SheafTorsor.Restriction
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import Mathlib.CategoryTheory.Category.Cat

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
    (P : Sheaf.Torsor ((restrictGrp U).obj 𝒢)) : (ofTorsor U P).U = U := rfl

/-- The constructor of `Obj` stores the supplied torsor. -/
theorem ofTorsor_P {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} (U : Over S)
    (P : Sheaf.Torsor ((restrictGrp U).obj 𝒢)) : (ofTorsor U P).P = P := rfl

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
  iso : Sheaf.Torsor.Iso (inverseImageTorsor f ξ'.P) ξ.P

/-- Assemble a morphism of `𝒢`-Torsors from a scheme map and an equivariant
carrier isomorphism. -/
def ofIso {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {ξ ξ' : Obj 𝒢}
    (f : ξ.U ⟶ ξ'.U) (g : (inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier)
    (h : IsEquivariant f g) : Hom ξ ξ' where
  f := f
  iso := Sheaf.Torsor.Iso.ofCarrierIso g h

/-- The constructor of `Hom` stores the supplied scheme map. -/
theorem ofIso_f {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {ξ ξ' : Obj 𝒢}
    (f : ξ.U ⟶ ξ'.U) (g : (inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier)
    (h : IsEquivariant f g) : (ofIso f g h).f = f := rfl

/-- The constructor of `Hom` stores the promoted torsor isomorphism. -/
theorem ofIso_iso {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {ξ ξ' : Obj 𝒢}
    (f : ξ.U ⟶ ξ'.U) (g : (inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier)
    (h : IsEquivariant f g) : (ofIso f g h).iso =
      (Sheaf.Torsor.Iso.ofCarrierIso g h :
        Sheaf.Torsor.Iso (inverseImageTorsor f ξ'.P) ξ.P) := rfl

/-- Identity morphisms of `𝒢`-Torsors. -/
def idHom {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} (ξ : Obj 𝒢) : Hom ξ ξ where
  f := 𝟙 ξ.U
  iso := inverseImageTorsorId ξ.P

/-- Composition of morphisms of `𝒢`-Torsors. -/
def compHom {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {ξ ξ' ξ'' : Obj 𝒢}
    (α : Hom ξ ξ') (β : Hom ξ' ξ'') : Hom ξ ξ'' where
  f := α.f ≫ β.f
  iso := @Iso.trans _ Sheaf.Torsor.category _ _ _
    (inverseImageTorsorComp α.f β.f ξ''.P)
    (@Iso.trans _ Sheaf.Torsor.category _ _ _ (inverseImageTorsorMap α.f β.iso) α.iso)

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
@[reducible]
def category (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}) :
    Category (Obj 𝒢) where
  Hom ξ ξ' := Hom ξ ξ'
  id ξ := idHom ξ
  comp α β := compHom α β
  id_comp := idHom_comp
  comp_id := compHom_id
  assoc := assocHom

/-- The bundled category of schemes over the base equipped with restricted torsors. -/
def cat (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}) : Cat :=
  ⟨Obj 𝒢, category 𝒢⟩

/-- The forgetful functor sends identity morphisms to identity morphisms. -/
theorem forget_map_id {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} (ξ : Obj 𝒢) :
    (idHom ξ).f = 𝟙 ξ.U := rfl

/-- The forgetful functor preserves composition. -/
theorem forget_map_comp {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {ξ ξ' ξ'' : Obj 𝒢} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (compHom α β).f = α.f ≫ β.f := rfl

/-- The forgetful functor `𝒢`-Torsors `⟶` `(Sch/S)_fppf`. -/
def forget (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}) : cat 𝒢 ⥤ Over S where
  obj ξ := ξ.U
  map α := α.f
  map_id := forget_map_id
  map_comp := forget_map_comp

/-- The forgetful functor sends `(U, ℱ)` to `U`. -/
theorem forget_obj {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} (ξ : Obj 𝒢) :
    (forget 𝒢).obj ξ = ξ.U := rfl

/-- The forgetful functor sends a morphism `(f, α)` to `f`. -/
theorem forget_map {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {ξ ξ' : Obj 𝒢} (α : Hom ξ ξ') : (forget 𝒢).map α = α.f := rfl

/-- The underlying carrier isomorphism of a morphism of restricted torsors. -/
def Hom.carrierIso {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}} {ξ ξ' : Obj 𝒢}
    (α : Hom ξ ξ') : (inverseImage α.f).obj ξ'.P.carrier ≅ ξ.P.carrier :=
  Sheaf.Torsor.Iso.toCarrierIso α.iso

/-- The carrier isomorphism of a morphism of `𝒢`-Torsors is equivariant. -/
theorem Hom.carrierIso_isEquivariant {𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}}
    {ξ ξ' : Obj 𝒢} (α : Hom ξ ξ') : IsEquivariant α.f (Hom.carrierIso α) :=
  (@Iso.hom _ Sheaf.Torsor.category _ _ α.iso).comm

/-- The forgetful functor `𝒢`-Torsors `⟶` `(Sch/S)_fppf` is fibered in groupoids. -/
instance instIsFiberedInGroupoids (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}) :
    Functor.IsFibered.InGroupoids (forget 𝒢) := sorry

end AlgebraicGeometry.SheafTorsors
