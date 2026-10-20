/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group.Sheaf
public import ReasLib.AlgebraicGeometry.SheafTorsor.Restriction
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Basic

/-!
# The category and stack of relative sheaf torsors
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace.SheafTorsors

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)

/-- An object of `𝒢/ℬ`-Torsors: a scheme `U` over `S`, a section of `ℬ` over `U`,
and a torsor under `U ×_{b,ℬ} 𝒢`. -/
structure Object (G : GroupAlgebraicSpace B) where
  /-- The underlying scheme over `S`. -/
  U : Over S
  /-- The section of `ℬ` over `U`. -/
  b : ofOver U ⟶ B
  /-- The sheaf torsor under `U ×_{b,ℬ} 𝒢`. -/
  P : Sheaf.Torsor (baseChangeGroupSheaf G b)

/-- Assemble an object of `𝒢/ℬ`-Torsors from a scheme, a section of `ℬ`, and a
sheaf torsor. -/
def ofTorsor (U : Over S) (b : ofOver U ⟶ B)
    (P : Sheaf.Torsor (baseChangeGroupSheaf G b)) : Object G where
  U := U
  b := b
  P := P

/-- The constructor of `Object` stores the supplied scheme, section, and torsor. -/
theorem ofTorsor_spec (U : Over S) (b : ofOver U ⟶ B)
    (P : Sheaf.Torsor (baseChangeGroupSheaf G b)) :
    (ofTorsor G U b P).U = U ∧ (ofTorsor G U b P).b = b ∧
      (ofTorsor G U b P).P = P := sorry

/-- A carrier isomorphism over `f` is equivariant if it intertwines the
`𝒢`-actions after identifying group sections along inverse image. -/
def IsEquivariant (ξ ξ' : Object G) (f : ξ.U ⟶ ξ'.U)
    (h : ξ.b = ofOverMap f ≫ ξ'.b)
    (g : (AlgebraicGeometry.SheafTorsors.inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier) : Prop :=
  ∀ (V : Over ξ.U.left)
    (gp : FiberPoint G ξ.b V)
    (x : ((AlgebraicGeometry.SheafTorsors.inverseImage f).obj ξ'.P.carrier).obj.obj (op V)),
    g.hom.hom.app (op V)
        ((ξ'.P.mulAction ((Over.map f.left).obj V)).smul
          (groupMulEquiv G f ξ'.b V (FiberPoint.transport G h gp)) x) =
      (ξ.P.mulAction V).smul gp (g.hom.hom.app (op V) x)

/-- A morphism of `𝒢/ℬ`-Torsors: a map of schemes over `B` and an equivariant
isomorphism `f⁻¹ℱ' ≅ ℱ` of sheaf torsors. -/
structure Hom {G : GroupAlgebraicSpace B} (ξ ξ' : Object G) where
  /-- The underlying morphism of schemes over `S`. -/
  f : ξ.U ⟶ ξ'.U
  /-- The morphism `f` lies over `ℬ`. -/
  comm : ξ.b = ofOverMap f ≫ ξ'.b
  /-- The isomorphism `f⁻¹ℱ' ≅ ℱ` of torsor carriers. -/
  g : (AlgebraicGeometry.SheafTorsors.inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier
  /-- The isomorphism `g` is equivariant for the group actions. -/
  equivariant : IsEquivariant G ξ ξ' f comm g

/-- Assemble a morphism from a scheme map and an equivariant carrier isomorphism. -/
def ofIso {ξ ξ' : Object G} (f : ξ.U ⟶ ξ'.U) (h : ξ.b = ofOverMap f ≫ ξ'.b)
    (g : (AlgebraicGeometry.SheafTorsors.inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier)
    (hg : IsEquivariant G ξ ξ' f h g) : Hom ξ ξ' where
  f := f
  comm := h
  g := g
  equivariant := hg

/-- The constructor of `Hom` stores the supplied scheme map, over-`ℬ` equality,
isomorphism, and equivariance witness. -/
theorem ofIso_spec {ξ ξ' : Object G} (f : ξ.U ⟶ ξ'.U)
    (h : ξ.b = ofOverMap f ≫ ξ'.b)
    (g : (AlgebraicGeometry.SheafTorsors.inverseImage f).obj ξ'.P.carrier ≅ ξ.P.carrier)
    (hg : IsEquivariant G ξ ξ' f h g) :
    (ofIso G f h g hg).f = f ∧ (ofIso G f h g hg).comm = h ∧
      (ofIso G f h g hg).g = g ∧ (ofIso G f h g hg).equivariant = hg := sorry

/-- Identity of schemes over `S` is compatible with the section of `ℬ`. -/
theorem id_comm (ξ : Object G) : ξ.b = ofOverMap (𝟙 ξ.U) ≫ ξ.b := sorry

/-- The identity comparison of torsor carriers is equivariant. -/
theorem id_equivariant (ξ : Object G) :
    IsEquivariant G ξ ξ (𝟙 ξ.U) (id_comm G ξ)
      ((AlgebraicGeometry.SheafTorsors.inverseImageId ξ.U).app ξ.P.carrier) :=
  sorry

/-- Identity morphisms of `𝒢/ℬ`-Torsors. -/
def idHom (ξ : Object G) : Hom ξ ξ where
  f := 𝟙 ξ.U
  comm := id_comm G ξ
  g := (AlgebraicGeometry.SheafTorsors.inverseImageId ξ.U).app ξ.P.carrier
  equivariant := id_equivariant G ξ

/-- The composite isomorphism of torsor carriers along a composite of scheme maps. -/
def compIso {ξ ξ' ξ'' : Object G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (AlgebraicGeometry.SheafTorsors.inverseImage (α.f ≫ β.f)).obj ξ''.P.carrier ≅ ξ.P.carrier :=
  (AlgebraicGeometry.SheafTorsors.inverseImageComp α.f β.f).symm.app ξ''.P.carrier ≪≫
    (AlgebraicGeometry.SheafTorsors.inverseImage α.f).mapIso β.g ≪≫ α.g

/-- Compatibility of a composite morphism with the sections of `ℬ`. -/
theorem comp_comm {ξ ξ' ξ'' : Object G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    ξ.b = ofOverMap (α.f ≫ β.f) ≫ ξ''.b := sorry

/-- The composite isomorphism of torsor carriers is equivariant. -/
theorem comp_equivariant {ξ ξ' ξ'' : Object G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    IsEquivariant G ξ ξ'' (α.f ≫ β.f) (comp_comm G α β) (compIso G α β) := sorry

/-- Composition of morphisms of `𝒢/ℬ`-Torsors. -/
def compHom {ξ ξ' ξ'' : Object G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') : Hom ξ ξ'' where
  f := α.f ≫ β.f
  comm := comp_comm G α β
  g := compIso G α β
  equivariant := comp_equivariant G α β

/-- Left identity law for morphisms of `𝒢/ℬ`-Torsors. -/
theorem idHom_comp {ξ ξ' : Object G} (α : Hom ξ ξ') : compHom G (idHom G ξ) α = α := sorry

/-- Right identity law for morphisms of `𝒢/ℬ`-Torsors. -/
theorem compHom_id {ξ ξ' : Object G} (α : Hom ξ ξ') : compHom G α (idHom G ξ') = α := sorry

/-- Associativity of composition of morphisms of `𝒢/ℬ`-Torsors. -/
theorem assocHom {ξ₁ ξ₂ ξ₃ ξ₄ : Object G} (α : Hom ξ₁ ξ₂) (β : Hom ξ₂ ξ₃) (c : Hom ξ₃ ξ₄) :
    compHom G (compHom G α β) c = compHom G α (compHom G β c) := sorry

/-- The category of objects of `𝒢/ℬ`-Torsors. -/
@[reducible]
def category (G : GroupAlgebraicSpace B) : Category (Object G) where
  Hom ξ ξ' := Hom ξ ξ'
  id ξ := idHom G ξ
  comp α β := compHom G α β
  id_comp := idHom_comp G
  comp_id := compHom_id G
  assoc := assocHom G

/-- The bundled category of relative torsor triples. -/
def cat (G : GroupAlgebraicSpace B) : Cat :=
  ⟨Object G, category G⟩

/-- The objects of the bundled category of relative torsors. -/
abbrev Obj (G : GroupAlgebraicSpace B) : Type (u + 1) := cat G

/-- The forgetful functor sends identity morphisms to identity morphisms. -/
theorem forget_map_id (ξ : Obj G) : (idHom G ξ).f = 𝟙 ξ.U := sorry

/-- The forgetful functor preserves composition. -/
theorem forget_map_comp {ξ ξ' ξ'' : Obj G} (α : Hom ξ ξ') (β : Hom ξ' ξ'') :
    (compHom G α β).f = α.f ≫ β.f := sorry

/-- The forgetful functor from `𝒢/ℬ`-Torsors to `(Sch/S)_fppf`. -/
def forget (G : GroupAlgebraicSpace B) : Obj G ⥤ Over S where
  obj ξ := ξ.U
  map α := α.f
  map_id := forget_map_id G
  map_comp := forget_map_comp G

/-- The forgetful functor sends `(U, b, P)` to `U`. -/
theorem forget_obj (ξ : Obj G) : (forget G).obj ξ = ξ.U := sorry

/-- The forgetful functor sends a morphism `(f, g)` to `f`. -/
theorem forget_map {ξ ξ' : Obj G} (α : Hom ξ ξ') : (forget G).map α = α.f := sorry

/-- The forgetful functor is fibered in groupoids. -/
instance instIsFiberedInGroupoids : Functor.IsFibered.InGroupoids (forget G) := sorry

/-- The forgetful functor is a stack in groupoids on the big fppf site. -/
instance instIsStackInGroupoids :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (forget G) := sorry

/-- The stack in groupoids of `𝒢/ℬ`-torsors over `(Sch/S)_fppf`. -/
def stack (G : GroupAlgebraicSpace B) : StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjection (Scheme.fppfTopology.over S) (forget G)

/-- The projection of `stack` is the forgetful functor to `(Sch/S)_fppf`. -/
theorem stack_p : (stack G).p = forget G := sorry

end AlgebraicGeometry.GroupAlgebraicSpace.SheafTorsors
