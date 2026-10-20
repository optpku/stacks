module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap68.Definition_68_11_2_ResidueField
public import stacks_project.Chap68.Definition_68_11_5_Neighborhood
public import stacks_project.Chap70.Lemma_70_19_1_BaseChange
public import stacks_project.Chap71.Lemma_71_4_1_Fiber

/-!
# Comparison of field-valued fibres of morphisms of algebraic spaces

A commutative square induces a morphism of fibres over a field-valued point
of the domain of the base map. A factorization of field-valued points
induces a morphism of fibres of a fixed morphism. These paste to a
comparison along an étale neighbourhood.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism of fibres over a field-valued point induced by a commutative
square of algebraic spaces. -/
def fiberOver_mapSquare {S : Scheme.{u}} {Y Y' V W : AlgebraicSpace S}
    (f : Y ⟶ W) (a : V ⟶ W) (fst : Y' ⟶ Y) (g : Y' ⟶ V) (p : FieldValuedPoint V)
    (w : (fiberι g p ≫ fst) ≫ f = fiberToSpec g p ≫ (p.map a).hom) :
    fieldFiber g p ⟶ fieldFiber f (p.map a) :=
  pullback.lift (fiberι g p ≫ fst) (fiberToSpec g p) w

/-- The commutativity witness for `fiberOver_mapSquare` when the ambient square
commutes. -/
theorem fiberOver_mapSquare_condition {S : Scheme.{u}} {Y Y' V W : AlgebraicSpace S}
    (f : Y ⟶ W) (a : V ⟶ W) (fst : Y' ⟶ Y) (g : Y' ⟶ V) (p : FieldValuedPoint V)
    (hw : fst ≫ f = g ≫ a) :
    (fiberι g p ≫ fst) ≫ f = fiberToSpec g p ≫ (p.map a).hom :=
  sorry

/-- `fiberOver_mapSquare` recovers the given map to the source on first
projections, and is the identity on the maps to the source spectra. -/
theorem fiberOver_mapSquare_spec {S : Scheme.{u}} {Y Y' V W : AlgebraicSpace S}
    (f : Y ⟶ W) (a : V ⟶ W) (fst : Y' ⟶ Y) (g : Y' ⟶ V) (p : FieldValuedPoint V)
    (w : (fiberι g p ≫ fst) ≫ f = fiberToSpec g p ≫ (p.map a).hom) :
    fiberOver_mapSquare f a fst g p w ≫ fiberι f (p.map a) = fiberι g p ≫ fst ∧
      fiberOver_mapSquare f a fst g p w ≫ fiberToSpec f (p.map a) =
        fiberToSpec g p :=
  sorry

/-- The fibre comparison along a square is an isomorphism when the square is a
pullback. -/
theorem isIso_fiberOver_mapSquare {S : Scheme.{u}} {Y Y' V W : AlgebraicSpace S}
    (f : Y ⟶ W) (a : V ⟶ W) (fst : Y' ⟶ Y) (g : Y' ⟶ V) (p : FieldValuedPoint V)
    (w : (fiberι g p ≫ fst) ≫ f = fiberToSpec g p ≫ (p.map a).hom)
    (h : IsPullback fst g f a) : IsIso (fiberOver_mapSquare f a fst g p w) :=
  sorry

/-- The morphism of fibres of `f` induced by a factorization of field-valued
points of the target. -/
def fiberOver_factor {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    {p q : FieldValuedPoint X} (φ : p.Factorization q)
    (w : fiberι f p ≫ f =
      (fiberToSpec f p ≫ ofOverHomMk φ.schemeHom φ.fac_structure) ≫ q.hom) :
    fieldFiber f p ⟶ fieldFiber f q :=
  pullback.lift (fiberι f p)
    (fiberToSpec f p ≫ ofOverHomMk φ.schemeHom φ.fac_structure) w

/-- The commutativity witness for `fiberOver_factor` from the factorization
triangle over `X`. -/
theorem fiberOver_factor_condition {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) {p q : FieldValuedPoint X} (φ : p.Factorization q) :
    fiberι f p ≫ f =
      (fiberToSpec f p ≫ ofOverHomMk φ.schemeHom φ.fac_structure) ≫ q.hom :=
  sorry

/-- `fiberOver_factor` commutes with the projections to the source and with the
maps to the source spectra via `ofOverHomMk φ.schemeHom`. -/
theorem fiberOver_factor_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) {p q : FieldValuedPoint X} (φ : p.Factorization q)
    (w : fiberι f p ≫ f =
      (fiberToSpec f p ≫ ofOverHomMk φ.schemeHom φ.fac_structure) ≫ q.hom) :
    fiberOver_factor f φ w ≫ fiberι f q = fiberι f p ∧
      fiberOver_factor f φ w ≫ fiberToSpec f q =
        fiberToSpec f p ≫ ofOverHomMk φ.schemeHom φ.fac_structure :=
  sorry

/-- The fibre comparison along a factorization is an isomorphism when the
source-spectrum map is an isomorphism. -/
theorem isIso_fiberOver_factor {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) {p q : FieldValuedPoint X} (φ : p.Factorization q)
    (w : fiberι f p ≫ f =
      (fiberToSpec f p ≫ ofOverHomMk φ.schemeHom φ.fac_structure) ≫ q.hom)
    [IsIso φ.schemeHom] : IsIso (fiberOver_factor f φ w) :=
  sorry

/-- The composite comparison from the fibre of a base change along an étale
neighbourhood to the fibre of the original morphism over the residue-field
point. -/
def fiberOver_neighborhoodComparison {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] (f : Y ⟶ X) {x : Points X} (U : EtaleNeighborhood X x)
    (fst : overPullbackObj U.hom (Over.mk f) ⟶ Y)
    (φ : FieldValuedPoint.Factorization (EtaleNeighborhood.residuePoint U)
      (FieldValuedPoint.residuePoint x))
    (wSquare :
      (fiberι (overPullbackSnd U.hom (Over.mk f))
            (FieldValuedPoint.ofScheme
              (Scheme.FieldValuedPoint.residuePoint U.point)) ≫
          fst) ≫ f =
        fiberToSpec (overPullbackSnd U.hom (Over.mk f))
            (FieldValuedPoint.ofScheme
              (Scheme.FieldValuedPoint.residuePoint U.point)) ≫
          ((FieldValuedPoint.ofScheme
              (Scheme.FieldValuedPoint.residuePoint U.point)).map U.hom).hom)
    (wFactor :
      fiberι f (EtaleNeighborhood.residuePoint U) ≫ f =
        (fiberToSpec f (EtaleNeighborhood.residuePoint U) ≫
            ofOverHomMk φ.schemeHom φ.fac_structure) ≫
          (FieldValuedPoint.residuePoint x).hom) :
    fieldFiber (overPullbackSnd U.hom (Over.mk f))
        (FieldValuedPoint.ofScheme
          (Scheme.FieldValuedPoint.residuePoint U.point)) ⟶
      fieldFiber f (FieldValuedPoint.residuePoint x) :=
  fiberOver_mapSquare f U.hom fst (overPullbackSnd U.hom (Over.mk f))
      (FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint U.point))
      wSquare ≫
    fiberOver_factor f φ wFactor

/-- `fiberOver_neighborhoodComparison` is the composite of `fiberOver_mapSquare`
with `fiberOver_factor`, and the resulting triangle with `fiberι` is the
first-projection pasting of the square. -/
theorem fiberOver_neighborhoodComparison_spec {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsDecent X] (f : Y ⟶ X) {x : Points X}
    (U : EtaleNeighborhood X x) (fst : overPullbackObj U.hom (Over.mk f) ⟶ Y)
    (φ : FieldValuedPoint.Factorization (EtaleNeighborhood.residuePoint U)
      (FieldValuedPoint.residuePoint x))
    (wSquare :
      (fiberι (overPullbackSnd U.hom (Over.mk f))
            (FieldValuedPoint.ofScheme
              (Scheme.FieldValuedPoint.residuePoint U.point)) ≫
          fst) ≫ f =
        fiberToSpec (overPullbackSnd U.hom (Over.mk f))
            (FieldValuedPoint.ofScheme
              (Scheme.FieldValuedPoint.residuePoint U.point)) ≫
          ((FieldValuedPoint.ofScheme
              (Scheme.FieldValuedPoint.residuePoint U.point)).map U.hom).hom)
    (wFactor :
      fiberι f (EtaleNeighborhood.residuePoint U) ≫ f =
        (fiberToSpec f (EtaleNeighborhood.residuePoint U) ≫
            ofOverHomMk φ.schemeHom φ.fac_structure) ≫
          (FieldValuedPoint.residuePoint x).hom) :
    fiberOver_neighborhoodComparison f U fst φ wSquare wFactor =
        fiberOver_mapSquare f U.hom fst (overPullbackSnd U.hom (Over.mk f))
            (FieldValuedPoint.ofScheme
              (Scheme.FieldValuedPoint.residuePoint U.point))
            wSquare ≫
          fiberOver_factor f φ wFactor ∧
      fiberOver_neighborhoodComparison f U fst φ wSquare wFactor ≫
          fiberι f (FieldValuedPoint.residuePoint x) =
        fiberι (overPullbackSnd U.hom (Over.mk f))
            (FieldValuedPoint.ofScheme
              (Scheme.FieldValuedPoint.residuePoint U.point)) ≫
          fst :=
  sorry

/-- The neighbourhood fibre comparison is an isomorphism when the base-change
square is a pullback and the residue-field factorization is an isomorphism of
source spectra. -/
theorem isIso_fiberOver_neighborhoodComparison {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsDecent X] (f : Y ⟶ X) {x : Points X}
    (U : EtaleNeighborhood X x) (fst : overPullbackObj U.hom (Over.mk f) ⟶ Y)
    (φ : FieldValuedPoint.Factorization (EtaleNeighborhood.residuePoint U)
      (FieldValuedPoint.residuePoint x))
    (wSquare :
      (fiberι (overPullbackSnd U.hom (Over.mk f))
            (FieldValuedPoint.ofScheme
              (Scheme.FieldValuedPoint.residuePoint U.point)) ≫
          fst) ≫ f =
        fiberToSpec (overPullbackSnd U.hom (Over.mk f))
            (FieldValuedPoint.ofScheme
              (Scheme.FieldValuedPoint.residuePoint U.point)) ≫
          ((FieldValuedPoint.ofScheme
              (Scheme.FieldValuedPoint.residuePoint U.point)).map U.hom).hom)
    (wFactor :
      fiberι f (EtaleNeighborhood.residuePoint U) ≫ f =
        (fiberToSpec f (EtaleNeighborhood.residuePoint U) ≫
            ofOverHomMk φ.schemeHom φ.fac_structure) ≫
          (FieldValuedPoint.residuePoint x).hom)
    (h : IsPullback fst (overPullbackSnd U.hom (Over.mk f)) f U.hom)
    [IsIso φ.schemeHom] :
    IsIso (fiberOver_neighborhoodComparison f U fst φ wSquare wFactor) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
