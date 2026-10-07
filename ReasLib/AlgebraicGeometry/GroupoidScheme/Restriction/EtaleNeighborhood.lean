module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import ReasLib.AlgebraicGeometry.GroupoidScheme.BaseChange
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

/-!
# Finite clopen restrictions after an étale base change

This module records an étale-local finiteness result for restrictions of groupoid schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom.FiniteType

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- A pointed groupoid scheme with finite source fibre and quasi-finite object map at the point
admits, after an elementary étale base change, a finite groupoid scheme embedded by open and
closed immersions whose distinguished object and arrow fibres are its source-target orbit
fibres. -/
@[stacks 03FL]
theorem exists_finiteClopenEmbeddedSubgroupoid_etaleNeighborhood {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left)
    [LocallyOfFiniteType G.U.hom] [IsSeparated G.U.hom] [IsSeparated G.R.hom]
    [Flat G.s.left] [Flat G.t.left]
    [LocallyOfFinitePresentation G.s.left] [LocallyOfFinitePresentation G.t.left]
    (h_quasiFinite : QuasiFiniteAt G.U.hom u)
    (h_sourceFinite : Set.Finite (G.s.left ⁻¹' ({u} : Set G.U.left))) :
    ∃ E : EtaleNeighborhood.Elementary S (G.U.hom u),
      let V := E.obj
      let G' := baseChange V.toEtale.hom G
      ∃ (H : GroupoidScheme V.toEtale.left) (ι : GroupoidScheme.Hom H G'),
        IsOpenImmersion ι.obj.left ∧
          IsClosedImmersion ι.obj.left ∧
          IsOpenImmersion ι.arrow.left ∧
          IsClosedImmersion ι.arrow.left ∧
          IsFinite H.U.hom ∧
          IsFinite H.R.hom ∧
          ∃ u' : H.U.left,
            H.U.hom u' = V.point ∧
              (ι.obj.left ≫ (baseChangeProjection V.toEtale.hom G).obj.left) u' = u ∧
              H.U.hom ⁻¹' ({V.point} : Set V.toEtale.left) =
                H.t.left '' (H.s.left ⁻¹' ({u'} : Set H.U.left)) ∧
              H.R.hom ⁻¹' ({V.point} : Set V.toEtale.left) =
                H.s.left ⁻¹' (H.U.hom ⁻¹' ({V.point} : Set V.toEtale.left)) := sorry

/-- A pointed groupoid scheme with finite source fibre and quasi-finite object map at the
point admits, after an elementary étale base change, a finite clopen canonical restriction
whose distinguished object and arrow fibres are the prescribed source-target orbit fibres. -/
@[stacks 03X5]
theorem exists_finiteClopenRestriction_etaleNeighborhood {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.U.left)
    [LocallyOfFiniteType G.U.hom] [IsSeparated G.U.hom] [IsSeparated G.R.hom]
    [Flat G.s.left] [Flat G.t.left]
    [LocallyOfFinitePresentation G.s.left] [LocallyOfFinitePresentation G.t.left]
    [UniversallyClosed G.toPreRelation.hom.left]
    (h_quasiFinite : QuasiFiniteAt G.U.hom u)
    (h_sourceFinite : Set.Finite (G.s.left ⁻¹' ({u} : Set G.U.left))) :
    ∃ E : EtaleNeighborhood.Elementary S (G.U.hom u),
      let V := E.obj
      let G' := baseChange V.toEtale.hom G
      ∃ (U' : Over V.toEtale.left) (g : U' ⟶ G'.U),
        IsOpenImmersion g.left ∧
          IsClosedImmersion g.left ∧
          IsOpenImmersion (G'.pullbackHom g).arrow.left ∧
          IsClosedImmersion (G'.pullbackHom g).arrow.left ∧
          IsFinite U'.hom ∧
          IsFinite (G'.pullback g).R.hom ∧
          ∃ u' : U'.left,
            U'.hom u' = V.point ∧
              (g.left ≫ (baseChangeProjection V.toEtale.hom G).obj.left) u' = u ∧
              U'.hom ⁻¹' ({V.point} : Set V.toEtale.left) =
                (G'.pullback g).t.left '' ((G'.pullback g).s.left ⁻¹' ({u'} : Set U'.left)) ∧
              (G'.pullback g).R.hom ⁻¹' ({V.point} : Set V.toEtale.left) =
                (G'.pullback g).s.left ⁻¹'
                  (U'.hom ⁻¹' ({V.point} : Set V.toEtale.left)) := sorry

end AlgebraicGeometry.GroupoidScheme
