module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.AlgebraicGeometry.SheafTorsor.Relative.Group
public import Mathlib.CategoryTheory.Category.Cat

/-!
# The fibered category of relative sheaf torsors

Objects of `𝒢/ℬ-Torsors` are triples `(U, b, ℱ)` with `ℱ` a
`U ×_{b,ℬ} 𝒢`-torsor on `(Sch/U)_fppf`. Morphisms are pairs `(f, g)` with
`b = b' ∘ f` and `g : f⁻¹ℱ' ≅ ℱ` an equivariant isomorphism of sheaves.
The forgetful functor sends `(U, b, ℱ)` to `U`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.SheafTorsors (inverseImage inverseImageId inverseImageComp)

noncomputable section

universe u

namespace AlgebraicGeometry.SheafTorsorsOver

variable {S : Scheme.{u}} {ℬ : Sheaf (Scheme.fppfTopology.over S) (Type u)}
variable (𝒢 : Grp (Over ℬ))

/-- An object of `𝒢/ℬ-Torsors`: a scheme `U` over `S`, a section of `ℬ` over
`U`, and a torsor under `U ×_{b,ℬ} 𝒢`. -/
structure Obj (𝒢 : Grp (Over ℬ)) where
  /-- The underlying scheme over `S`. -/
  U : Over S
  /-- The section of `ℬ` over `U`. -/
  b : ℬ.obj.obj (op U)
  /-- The sheaf torsor under `U ×_{b,ℬ} 𝒢`. -/
  P : Sheaf.Torsor (baseChangeGroupSheaf 𝒢 b)

/-- Assemble an object of `𝒢/ℬ-Torsors` from a scheme, a section of `ℬ`, and a
sheaf torsor. -/
def ofTorsor (U : Over S) (b : ℬ.obj.obj (op U))
    (P : Sheaf.Torsor (baseChangeGroupSheaf 𝒢 b)) : Obj 𝒢 where
  U := U
  b := b
  P := P

/-- The constructor of `Obj` stores the supplied scheme. -/
theorem ofTorsor_U (U : Over S) (b : ℬ.obj.obj (op U))
    (P : Sheaf.Torsor (baseChangeGroupSheaf 𝒢 b)) : (ofTorsor 𝒢 U b P).U = U := rfl

/-- The constructor of `Obj` stores the supplied section of `ℬ`. -/
theorem ofTorsor_b (U : Over S) (b : ℬ.obj.obj (op U))
    (P : Sheaf.Torsor (baseChangeGroupSheaf 𝒢 b)) : (ofTorsor 𝒢 U b P).b = b := rfl

/-- The constructor of `Obj` stores the supplied torsor. -/
theorem ofTorsor_P (U : Over S) (b : ℬ.obj.obj (op U))
    (P : Sheaf.Torsor (baseChangeGroupSheaf 𝒢 b)) : (ofTorsor 𝒢 U b P).P = P := rfl

/-- A carrier isomorphism over `f` is equivariant if it intertwines the
`𝒢`-actions after identifying group sections along inverse image. -/
def IsEquivariant (ξ ξ' : Obj 𝒢) (f : ξ.U ⟶ ξ'.U)
    (h : ξ.b = ℬ.obj.map f.op ξ'.b)
    (g : (inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier) : Prop :=
  ∀ (V : Over ξ.U.left)
    (gp : FiberPoint 𝒢 ξ.b V)
    (x : ((inverseImage f).obj ξ'.P.carrier).obj.obj (op V)),
    g.hom.hom.app (op V)
        ((ξ'.P.mulAction ((Over.map f.left).obj V)).smul
          (groupMulEquiv 𝒢 f ξ'.b V (FiberPoint.transport 𝒢 h gp)) x) =
      (ξ.P.mulAction V).smul gp (g.hom.hom.app (op V) x)

/-- A morphism of `𝒢/ℬ-Torsors`: a map of schemes over `S` and an equivariant
isomorphism `f⁻¹ℱ' ≅ ℱ` of sheaf torsors. -/
structure Hom {𝒢 : Grp (Over ℬ)} (ξ ξ' : Obj 𝒢) where
  /-- The underlying morphism of schemes over `S`. -/
  f : ξ.U ⟶ ξ'.U
  /-- The morphism `f` lies over `ℬ`. -/
  comm : ξ.b = ℬ.obj.map f.op ξ'.b
  /-- The underlying isomorphism of torsor carriers. -/
  g : (inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier
  /-- The isomorphism `g` is equivariant for the group actions. -/
  equivariant : IsEquivariant 𝒢 ξ ξ' f comm g

/-- Assemble a morphism from a scheme map and an equivariant carrier isomorphism. -/
def ofIso {ξ ξ' : Obj 𝒢} (f : ξ.U ⟶ ξ'.U) (h : ξ.b = ℬ.obj.map f.op ξ'.b)
    (g : (inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier)
    (hg : IsEquivariant 𝒢 ξ ξ' f h g) : Hom ξ ξ' where
  f := f
  comm := h
  g := g
  equivariant := hg

/-- The constructor of `Hom` stores the supplied scheme map. -/
theorem ofIso_f {ξ ξ' : Obj 𝒢} (f : ξ.U ⟶ ξ'.U)
    (h : ξ.b = ℬ.obj.map f.op ξ'.b)
    (g : (inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier)
    (hg : IsEquivariant 𝒢 ξ ξ' f h g) : (ofIso 𝒢 f h g hg).f = f := rfl

/-- Identity morphisms of `𝒢/ℬ-Torsors`. -/
def idHom (ξ : Obj 𝒢) : Hom ξ ξ where
  f := 𝟙 ξ.U
  comm := sorry
  g := (inverseImageId ξ.U).app ξ.P.carrier
  equivariant := sorry

/-- The composite isomorphism of torsor carriers along a composite of scheme maps. -/
def compIso {ξ ξ' ξ'' : Obj 𝒢} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (inverseImage (α.f ≫ β.f)).obj ξ''.P.carrier ≅ ξ.P.carrier :=
  (inverseImageComp α.f β.f).symm.app ξ''.P.carrier ≪≫
    (inverseImage α.f).mapIso β.g ≪≫ α.g

/-- Composition of morphisms of `𝒢/ℬ-Torsors`. -/
def compHom {ξ ξ' ξ'' : Obj 𝒢} (α : Hom ξ ξ') (β : Hom ξ' ξ'') : Hom ξ ξ'' where
  f := α.f ≫ β.f
  comm := sorry
  g := compIso 𝒢 α β
  equivariant := sorry

/-- Left identity law for morphisms of `𝒢/ℬ-Torsors`. -/
theorem idHom_comp {ξ ξ' : Obj 𝒢} (α : Hom ξ ξ') : compHom 𝒢 (idHom 𝒢 ξ) α = α := sorry

/-- Right identity law for morphisms of `𝒢/ℬ-Torsors`. -/
theorem compHom_id {ξ ξ' : Obj 𝒢} (α : Hom ξ ξ') : compHom 𝒢 α (idHom 𝒢 ξ') = α := sorry

/-- Associativity of composition of morphisms of `𝒢/ℬ-Torsors`. -/
theorem assocHom {ξ₁ ξ₂ ξ₃ ξ₄ : Obj 𝒢} (α : Hom ξ₁ ξ₂) (β : Hom ξ₂ ξ₃) (c : Hom ξ₃ ξ₄) :
    compHom 𝒢 (compHom 𝒢 α β) c = compHom 𝒢 α (compHom 𝒢 β c) := sorry

/-- The category of objects of `𝒢/ℬ-Torsors`. -/
@[reducible]
def category : Category (Obj 𝒢) where
  Hom ξ ξ' := Hom ξ ξ'
  id ξ := idHom 𝒢 ξ
  comp α β := compHom 𝒢 α β
  id_comp := idHom_comp 𝒢
  comp_id := compHom_id 𝒢
  assoc := assocHom 𝒢

/-- The bundled category of relative torsors over schemes over the base. -/
def cat (𝒢 : Grp (Over ℬ)) : Cat :=
  ⟨Obj 𝒢, category 𝒢⟩

/-- The forgetful functor sends identity morphisms to identity morphisms. -/
theorem forget_map_id (ξ : Obj 𝒢) : (idHom 𝒢 ξ).f = 𝟙 ξ.U := rfl

/-- The forgetful functor preserves composition. -/
theorem forget_map_comp {ξ ξ' ξ'' : Obj 𝒢} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (compHom 𝒢 α β).f = α.f ≫ β.f := rfl

/-- The forgetful functor from `𝒢/ℬ-Torsors` to `(Sch/S)_fppf`. -/
def forget (𝒢 : Grp (Over ℬ)) : cat 𝒢 ⥤ Over S where
  obj ξ := ξ.U
  map α := α.f
  map_id := forget_map_id 𝒢
  map_comp := forget_map_comp 𝒢

/-- The forgetful functor sends `(U, b, ℱ)` to `U`. -/
theorem forget_obj (ξ : Obj 𝒢) : (forget 𝒢).obj ξ = ξ.U := rfl

/-- The forgetful functor sends a morphism `(f, g)` to `f`. -/
theorem forget_map {ξ ξ' : Obj 𝒢} (α : Hom ξ ξ') : (forget 𝒢).map α = α.f := rfl

/-- The forgetful functor `𝒢/ℬ-Torsors ⟶ (Sch/S)_fppf` is fibered in groupoids. -/
instance instIsFiberedInGroupoids : Functor.IsFibered.InGroupoids (forget 𝒢) := sorry

end AlgebraicGeometry.SheafTorsorsOver
