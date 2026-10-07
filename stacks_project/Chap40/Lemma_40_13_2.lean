module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.EtaleNeighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom.FiniteType

universe u

/- Lemma 40.13.2: under the hypotheses of Lemma 40.13.1 and universal closedness
of the arrow map, an elementary étale neighborhood admits a finite clopen canonical
restriction with the prescribed distinguished point and object and arrow fibres. -/
@[stacks 03X5] #check
  (AlgebraicGeometry.GroupoidScheme.exists_finiteClopenRestriction_etaleNeighborhood :
    ∀ {S : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S) (u : G.U.left)
      [LocallyOfFiniteType G.U.hom] [IsSeparated G.U.hom] [IsSeparated G.R.hom]
      [Flat G.s.left] [Flat G.t.left]
      [LocallyOfFinitePresentation G.s.left] [LocallyOfFinitePresentation G.t.left]
      [UniversallyClosed G.toPreRelation.hom.left],
      QuasiFiniteAt G.U.hom u →
        Set.Finite (G.s.left ⁻¹' ({u} : Set G.U.left)) →
          ∃ E : EtaleNeighborhood.Elementary S (G.U.hom u),
            let V := E.obj
            let G' := AlgebraicGeometry.GroupoidScheme.baseChange V.toEtale.hom G
            ∃ (U' : Over V.toEtale.left) (g : U' ⟶ G'.U),
              IsOpenImmersion g.left ∧
                IsClosedImmersion g.left ∧
                IsOpenImmersion (G'.pullbackHom g).arrow.left ∧
                IsClosedImmersion (G'.pullbackHom g).arrow.left ∧
                IsFinite U'.hom ∧
                IsFinite (G'.pullback g).R.hom ∧
                ∃ u' : U'.left,
                  U'.hom u' = V.point ∧
                    (g.left ≫
                      (AlgebraicGeometry.GroupoidScheme.baseChangeProjection
                        V.toEtale.hom G).obj.left) u' = u ∧
                    U'.hom ⁻¹' ({V.point} : Set V.toEtale.left) =
                      (G'.pullback g).t.left ''
                        ((G'.pullback g).s.left ⁻¹' ({u'} : Set U'.left)) ∧
                    (G'.pullback g).R.hom ⁻¹' ({V.point} : Set V.toEtale.left) =
                      (G'.pullback g).s.left ⁻¹'
                        (U'.hom ⁻¹' ({V.point} : Set V.toEtale.left)))
