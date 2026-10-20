module

public import ReasLib.AlgebraicGeometry.Hilbert.Functor
public import ReasLib.CategoryTheory.RepresentablePresheaf
public import ReasLib.AlgebraicGeometry.Scheme.WeilRestriction.ClosedImmersion

/-!
# Closed immersions and Hilbert points

This file defines the map on degree-`d` Hilbert points induced by a closed immersion of
ambient schemes over a fixed base and relates it to explicit representations of the Hilbert
functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Hilbert

variable {S : Scheme.{u}}

/-- Mapping the ideal of a Hilbert point along the base change of a closed immersion
preserves its finite-locally-free rank over the parameter scheme. -/
theorem Point.map_finiteLocallyFree {X Y T : Over S} (i : X ⟶ Y)
    [IsClosedImmersion i.left] {d : ℕ} (p : Point X d T) :
    IsFiniteLocallyFreeOfRank
      ((p.ideal.map ((Over.pullback T.hom).map i).left).subschemeι ≫
        pullback.snd Y.hom T.hom) d := sorry

/-- Map a Hilbert point through a closed immersion of its ambient scheme. -/
def Point.map {X Y T : Over S} (i : X ⟶ Y) [IsClosedImmersion i.left]
    {d : ℕ} (p : Point X d T) : Point Y d T where
  ideal := p.ideal.map ((Over.pullback T.hom).map i).left
  finiteLocallyFree := p.map_finiteLocallyFree i

/-- The ideal of a mapped Hilbert point is the direct image along the base-changed ambient
closed immersion. -/
theorem Point.map_ideal {X Y T : Over S} (i : X ⟶ Y) [IsClosedImmersion i.left]
    {d : ℕ} (p : Point X d T) :
    (p.map i).ideal = p.ideal.map ((Over.pullback T.hom).map i).left := sorry

/-- Mapping Hilbert points through a closed immersion is natural in the parameter scheme. -/
theorem closedImmersionMap_naturality {X Y : Over S} (i : X ⟶ Y)
    [IsClosedImmersion i.left] (d : ℕ) {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    (functor X d).map f ≫
        TypeCat.ofHom (fun p : Point X d T'.unop ↦ p.map i) =
      TypeCat.ofHom (fun p : Point X d T.unop ↦ p.map i) ≫
        (functor Y d).map f := sorry

/-- A closed immersion of ambient schemes induces a natural transformation of their
degree-`d` Hilbert functors. -/
def closedImmersionMap {X Y : Over S} (i : X ⟶ Y) [IsClosedImmersion i.left]
    (d : ℕ) : functor X d ⟶ functor Y d where
  app T := TypeCat.ofHom (fun p : Point X d T.unop ↦ p.map i)
  naturality := fun _ _ f ↦ closedImmersionMap_naturality i d f

/-- The component of the closed-immersion transformation maps each Hilbert point through
the base-changed closed immersion. -/
theorem closedImmersionMap_app {X Y : Over S} (i : X ⟶ Y)
    [IsClosedImmersion i.left] (d : ℕ) (T : (Over S)ᵒᵖ) (p : Point X d T.unop) :
    (closedImmersionMap i d).app T p = p.map i := sorry

/-- If the degree-`d` Hilbert functor of `Y` is explicitly represented, then the degree-`d`
Hilbert functor of a closed subscheme `X` is explicitly represented, and the induced morphism
between the representing schemes is a closed immersion. -/
theorem exists_closedImmersion_representation {S : Scheme.{u}} {X Y : Over S}
    (i : X ⟶ Y) [IsClosedImmersion i.left] (d : ℕ) {HY : Over S}
    (RY : (functor Y d).RepresentableBy HY) :
    ∃ (HX : Over S) (RX : (functor X d).RepresentableBy HX),
      IsClosedImmersion (RX.map RY (closedImmersionMap i d)).left := sorry

end AlgebraicGeometry.Hilbert
