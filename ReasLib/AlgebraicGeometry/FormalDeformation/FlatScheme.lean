/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# Flat schemes over Artinian local algebras
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

noncomputable section

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatSchemeCat

/-- An Artinian local algebra together with a scheme flat over its spectrum. -/
structure Object where
  /-- The Artinian local base algebra. -/
  base : ArtinianLocalAlgCat Λ k
  /-- The scheme over the base algebra. -/
  scheme : Scheme.{u}
  /-- The structure morphism to the spectrum of the base algebra. -/
  structureHom : scheme ⟶ Spec (CommRingCat.of base.carrier)
  /-- The structure morphism is flat. -/
  isFlat : AlgebraicGeometry.Flat structureHom

/-- Construct explicit flat-scheme data from a base, a scheme, and a flat structure map. -/
def Object.of (base : ArtinianLocalAlgCat Λ k) (scheme : Scheme.{u})
    (structureHom : scheme ⟶ Spec (CommRingCat.of base.carrier))
    (isFlat : AlgebraicGeometry.Flat structureHom) : Object Λ k :=
  ⟨base, scheme, structureHom, isFlat⟩

end FlatSchemeCat

/-- The categorical interface of schemes flat over Artinian local algebras. -/
def FlatSchemeCat := FlatSchemeCat.Object Λ k

namespace FlatSchemeCat

variable {Λ k}

/-- The base algebra of a flat scheme. -/
def base (P : FlatSchemeCat Λ k) : ArtinianLocalAlgCat Λ k := Object.base P

/-- The underlying scheme of a flat scheme over an Artinian local algebra. -/
def scheme (P : FlatSchemeCat Λ k) : Scheme.{u} := Object.scheme P

/-- The structure map of a flat scheme to the spectrum of its base algebra. -/
def structureHom (P : FlatSchemeCat Λ k) : P.scheme ⟶ Spec (CommRingCat.of P.base.carrier) :=
  Object.structureHom P

/-- The stored flatness proof of the structure map of a flat scheme. -/
abbrev flatness (P : FlatSchemeCat Λ k) : AlgebraicGeometry.Flat P.structureHom :=
  Object.isFlat P

/-- Pair an Artinian local algebra with a scheme flat over its spectrum. -/
def of (A : ArtinianLocalAlgCat Λ k) (X : Scheme.{u})
    (structureHom : X ⟶ Spec (CommRingCat.of A.carrier))
    (isFlat : AlgebraicGeometry.Flat structureHom) : FlatSchemeCat Λ k :=
  Object.of Λ k A X structureHom isFlat

/-- The structure morphism of an object in the flat-scheme category is flat. -/
theorem spec (P : FlatSchemeCat Λ k) : AlgebraicGeometry.Flat P.structureHom := sorry

/-- The contravariant spectrum map induced by a morphism of Artinian local algebras. -/
def specMap {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    Spec (CommRingCat.of B.carrier) ⟶ Spec (CommRingCat.of A.carrier) :=
  Spec.map (CommRingCat.ofHom (ArtinianLocalAlgCat.Hom.toRingHom f))

/-- The spectrum map of an identity algebra morphism is the identity. -/
theorem specMap_id (A : ArtinianLocalAlgCat Λ k) :
    specMap (𝟙 A) = 𝟙 (Spec (CommRingCat.of A.carrier)) := sorry

/-- The spectrum map reverses composition of algebra morphisms. -/
theorem specMap_comp {A B C : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) (g : B ⟶ C) :
    specMap (f ≫ g) = specMap g ≫ specMap f := sorry

/-- A base-algebra map and a reversed scheme map forming a cartesian spectrum square. -/
structure Arrow (src tgt : FlatSchemeCat Λ k) where
  /-- The morphism of base algebras. -/
  baseHom : src.base ⟶ tgt.base
  /-- The reversed morphism of schemes. -/
  schemeHom : tgt.scheme ⟶ src.scheme
  /-- The spectrum square is cartesian. -/
  isPullback : IsPullback schemeHom tgt.structureHom src.structureHom (specMap baseHom)

/-- Construct explicit arrow data from a cartesian spectrum square. -/
def Arrow.of {src tgt : FlatSchemeCat Λ k} (baseHom : src.base ⟶ tgt.base)
    (schemeHom : tgt.scheme ⟶ src.scheme)
    (isPullback : IsPullback schemeHom tgt.structureHom src.structureHom (specMap baseHom)) :
    Arrow src tgt :=
  ⟨baseHom, schemeHom, isPullback⟩

/-- The categorical interface of cartesian morphisms between flat schemes. -/
def Hom (src tgt : FlatSchemeCat Λ k) := Arrow src tgt

namespace Hom

/-- The base-algebra map underlying a cartesian flat-scheme morphism. -/
def baseHom {src tgt : FlatSchemeCat Λ k} (f : Hom src tgt) : src.base ⟶ tgt.base :=
  Arrow.baseHom f

/-- The reversed scheme map underlying a cartesian flat-scheme morphism. -/
def schemeHom {src tgt : FlatSchemeCat Λ k} (f : Hom src tgt) : tgt.scheme ⟶ src.scheme :=
  Arrow.schemeHom f

/-- The cartesian spectrum square of a flat-scheme morphism. -/
abbrev isPullback {src tgt : FlatSchemeCat Λ k} (f : Hom src tgt) :
    IsPullback f.schemeHom tgt.structureHom src.structureHom (specMap f.baseHom) :=
  Arrow.isPullback f

/-- Construct a cartesian flat-scheme morphism from its base and scheme maps. -/
def of {src tgt : FlatSchemeCat Λ k} (baseHom : src.base ⟶ tgt.base)
    (schemeHom : tgt.scheme ⟶ src.scheme)
    (isPullback : IsPullback schemeHom tgt.structureHom src.structureHom (specMap baseHom)) :
    Hom src tgt :=
  Arrow.of baseHom schemeHom isPullback

/-- Identity base and scheme maps form a cartesian spectrum square. -/
theorem id_isPullback (P : FlatSchemeCat Λ k) :
    IsPullback (𝟙 P.scheme) P.structureHom P.structureHom (specMap (𝟙 P.base)) := sorry

/-- The composite of two cartesian spectrum squares is cartesian. -/
theorem comp_isPullback {src mid tgt : FlatSchemeCat Λ k} (f : Hom src mid) (g : Hom mid tgt) :
    IsPullback (g.schemeHom ≫ f.schemeHom) tgt.structureHom src.structureHom
      (specMap (f.baseHom ≫ g.baseHom)) := sorry

/-- The identity cartesian morphism of a flat scheme. -/
def id (P : FlatSchemeCat Λ k) : Hom P P :=
  of (𝟙 P.base) (𝟙 P.scheme) (id_isPullback P)

/-- Compose base maps in order and scheme maps in reverse order. -/
def comp {src mid tgt : FlatSchemeCat Λ k} (f : Hom src mid) (g : Hom mid tgt) : Hom src tgt :=
  of (f.baseHom ≫ g.baseHom) (g.schemeHom ≫ f.schemeHom) (comp_isPullback f g)

/-- A cartesian flat-scheme morphism has a commuting and cartesian spectrum square. -/
theorem spec {src tgt : FlatSchemeCat Λ k} (f : Hom src tgt) :
    f.schemeHom ≫ src.structureHom = tgt.structureHom ≫ specMap f.baseHom ∧
      IsPullback f.schemeHom tgt.structureHom src.structureHom (specMap f.baseHom) := sorry

/-- The identity flat-scheme morphism has identity base map. -/
theorem id_baseHom (P : FlatSchemeCat Λ k) : (id P).baseHom = 𝟙 P.base := sorry

/-- The base map of a composite is the composite of the base maps. -/
theorem comp_baseHom {src mid tgt : FlatSchemeCat Λ k} (f : Hom src mid)
    (g : Hom mid tgt) : (comp f g).baseHom = f.baseHom ≫ g.baseHom := sorry

/-- The identity cartesian morphism is a left identity for composition. -/
theorem id_comp {src tgt : FlatSchemeCat Λ k} (f : Hom src tgt) : comp (id src) f = f := sorry

/-- The identity cartesian morphism is a right identity for composition. -/
theorem comp_id {src tgt : FlatSchemeCat Λ k} (f : Hom src tgt) : comp f (id tgt) = f := sorry

/-- Composition of cartesian flat-scheme morphisms is associative. -/
theorem assoc {first second third fourth : FlatSchemeCat Λ k}
    (f : Hom first second) (g : Hom second third) (h : Hom third fourth) :
    comp (comp f g) h = comp f (comp g h) := sorry

end Hom

/-- Flat schemes over Artinian local algebras form a category with cartesian morphisms. -/
instance category : Category.{u} (FlatSchemeCat Λ k) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

section Forget

variable (Λ k)

/-- The projection of a flat scheme to its Artinian local base algebra. -/
def forget : FlatSchemeCat Λ k ⥤ ArtinianLocalAlgCat Λ k where
  obj := base
  map := Hom.baseHom
  map_id := Hom.id_baseHom
  map_comp := Hom.comp_baseHom

/-- The projection functor selects the stored base algebra. -/
theorem forget_obj (P : FlatSchemeCat Λ k) : (forget Λ k).obj P = P.base := sorry

/-- The projection functor selects the stored base morphism. -/
theorem forget_map {src tgt : FlatSchemeCat Λ k} (f : src ⟶ tgt) :
    (forget Λ k).map f = f.baseHom := sorry

/-- The flat-scheme projection is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_forget : IsFibered.InGroupoids (forget Λ k).op := sorry

end Forget

end FlatSchemeCat
