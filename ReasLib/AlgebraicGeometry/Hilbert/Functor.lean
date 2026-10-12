/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic

/-!
# The Hilbert functor of finite locally free subschemes

This file defines the points and base-change maps of the Hilbert functor of
degree-`d` finite locally free closed subschemes.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Hilbert

variable {S : Scheme.{u}}

/-- The canonical map `X ×ₛ T' ⟶ X ×ₛ T` induced by a morphism `T' ⟶ T` over `S`. -/
def fiberMap (X : Over S) {T T' : Over S} (h : T' ⟶ T) :
    pullback X.hom T'.hom ⟶ pullback X.hom T.hom :=
  pullback.map X.hom T'.hom X.hom T.hom (𝟙 X.left) h.left (𝟙 S)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans h.w.symm)

/-- The map `fiberMap X h` commutes with the projections to `X`. -/
theorem fiberMap_fst (X : Over S) {T T' : Over S} (h : T' ⟶ T) :
    fiberMap X h ≫ pullback.fst X.hom T.hom = pullback.fst X.hom T'.hom := sorry

/-- The map `fiberMap X h` commutes with the projections to the varying base. -/
theorem fiberMap_snd (X : Over S) {T T' : Over S} (h : T' ⟶ T) :
    fiberMap X h ≫ pullback.snd X.hom T.hom =
      pullback.snd X.hom T'.hom ≫ h.left := sorry

/-- A degree-`d` Hilbert point of `X` over `T`: a closed subscheme of `X ×ₛ T`
whose structure morphism to `T` is finite locally free of rank `d`. -/
structure Point.{v} {S : Scheme.{v}} (X : Over S) (d : ℕ) (T : Over S) : Type v where
  /-- The ideal sheaf defining the closed subscheme of `X ×ₛ T`. -/
  ideal : (pullback X.hom T.hom).IdealSheafData
  /-- The closed subscheme is finite locally free of rank `d` over `T`. -/
  finiteLocallyFree : IsFiniteLocallyFreeOfRank
    (ideal.subschemeι ≫ pullback.snd X.hom T.hom) d

namespace Point

/-- Construct a Hilbert point from its ideal sheaf and finite-locally-free rank condition. -/
def ofIdeal (X : Over S) (d : ℕ) (T : Over S)
    (ideal : (pullback X.hom T.hom).IdealSheafData)
    (finiteLocallyFree : IsFiniteLocallyFreeOfRank
      (ideal.subschemeι ≫ pullback.snd X.hom T.hom) d) : Point X d T where
  ideal := ideal
  finiteLocallyFree := finiteLocallyFree

/-- The structure morphism from the closed subscheme represented by a Hilbert point to `T`. -/
def structureMap {X T : Over S} {d : ℕ} (p : Point X d T) :
    p.ideal.subscheme ⟶ T.left :=
  p.ideal.subschemeι ≫ pullback.snd X.hom T.hom

/-- The structure morphism of a Hilbert point is its closed immersion followed by the
second projection. -/
theorem structureMap_def {X T : Over S} {d : ℕ} (p : Point X d T) :
    p.structureMap = p.ideal.subschemeι ≫ pullback.snd X.hom T.hom := sorry

/-- A Hilbert point represents a closed subscheme whose structure morphism is finite locally
free of the specified rank. -/
theorem spec {X T : Over S} {d : ℕ} (p : Point X d T) :
    IsClosedImmersion p.ideal.subschemeι ∧ IsFiniteLocallyFreeOfRank p.structureMap d := sorry

/-- Pullback preserves the finite-locally-free rank condition of a Hilbert point. -/
theorem pullback_finiteLocallyFree {X T T' : Over S} {d : ℕ} (p : Point X d T)
    (h : T' ⟶ T) :
    IsFiniteLocallyFreeOfRank
      ((p.ideal.comap (fiberMap X h)).subschemeι ≫ pullback.snd X.hom T'.hom) d := sorry

/-- Pull a Hilbert point back along a morphism of schemes over the base. -/
def pullback {X T T' : Over S} {d : ℕ} (p : Point X d T) (h : T' ⟶ T) :
    Point X d T' where
  ideal := p.ideal.comap (fiberMap X h)
  finiteLocallyFree := pullback_finiteLocallyFree p h

/-- The ideal sheaf of a pulled-back Hilbert point is the comap along the canonical fiber map. -/
theorem pullback_ideal {X T T' : Over S} {d : ℕ} (p : Point X d T) (h : T' ⟶ T) :
    (p.pullback h).ideal = p.ideal.comap (fiberMap X h) := sorry

/-- Pulling a Hilbert point back along the identity morphism leaves it unchanged. -/
theorem pullback_id {X T : Over S} {d : ℕ} (p : Point X d T) :
    p.pullback (𝟙 T) = p := sorry

/-- Pullback of Hilbert points is compatible with composition. -/
theorem pullback_comp {X T T' T'' : Over S} {d : ℕ} (p : Point X d T)
    (h : T' ⟶ T) (k : T'' ⟶ T') :
    (p.pullback h).pullback k = p.pullback (k ≫ h) := sorry

end Point

/-- The maps defining the Hilbert functor preserve identity morphisms. -/
theorem functor_map_id (X : Over S) (d : ℕ) (T : (Over S)ᵒᵖ) :
    TypeCat.ofHom (fun p : Point X d T.unop ↦ p.pullback (𝟙 T).unop) =
      𝟙 (Point X d T.unop) := sorry

/-- The maps defining the Hilbert functor preserve composition. -/
theorem functor_map_comp (X : Over S) (d : ℕ) {T T' T'' : (Over S)ᵒᵖ}
    (h : T ⟶ T') (k : T' ⟶ T'') :
    TypeCat.ofHom (fun p : Point X d T.unop ↦ p.pullback (h ≫ k).unop) =
      TypeCat.ofHom (fun p : Point X d T.unop ↦ p.pullback h.unop) ≫
        TypeCat.ofHom (fun p : Point X d T'.unop ↦ p.pullback k.unop) := sorry

/-- The Hilbert functor assigning to `T ⟶ S` the degree-`d` finite locally free closed
subschemes of `X ×ₛ T`. -/
def functor (X : Over S) (d : ℕ) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Point X d T.unop
  map {T T'} h := TypeCat.ofHom (fun p : Point X d T.unop ↦ p.pullback h.unop)
  map_id := functor_map_id X d
  map_comp := functor_map_comp X d

/-- Evaluating the Hilbert functor at `T` gives the type of degree-`d` Hilbert points over `T`. -/
theorem functor_obj (X : Over S) (d : ℕ) (T : Over S) :
    (functor X d).obj (op T) = Point X d T := sorry

/-- The Hilbert functor acts on a morphism by scheme-theoretic base change. -/
theorem functor_map (X : Over S) (d : ℕ) {T T' : (Over S)ᵒᵖ} (h : T ⟶ T') :
    (functor X d).map h =
      TypeCat.ofHom (fun p : Point X d T.unop ↦ p.pullback h.unop) := sorry

end AlgebraicGeometry.Hilbert
