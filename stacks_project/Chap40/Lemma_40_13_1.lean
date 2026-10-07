module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.EtaleNeighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom.FiniteType

universe u

/- Lemma 40.13.1: a pointed groupoid scheme satisfying the stated finiteness,
separatedness, flatness, and presentation hypotheses admits, after an elementary étale
base change, a finite clopen embedded subgroupoid with the prescribed orbit fibres. -/
@[stacks 03FL] #check
  (AlgebraicGeometry.GroupoidScheme.exists_finiteClopenEmbeddedSubgroupoid_etaleNeighborhood :
    ∀ {S : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S) (u : G.U.left)
      [LocallyOfFiniteType G.U.hom] [IsSeparated G.U.hom] [IsSeparated G.R.hom]
      [Flat G.s.left] [Flat G.t.left]
      [LocallyOfFinitePresentation G.s.left] [LocallyOfFinitePresentation G.t.left],
      QuasiFiniteAt G.U.hom u →
        Set.Finite (G.s.left ⁻¹' ({u} : Set G.U.left)) →
          ∃ E : EtaleNeighborhood.Elementary S (G.U.hom u),
            let V := E.obj
            let G' := AlgebraicGeometry.GroupoidScheme.baseChange V.toEtale.hom G
            ∃ (H : AlgebraicGeometry.GroupoidScheme V.toEtale.left)
                (ι : AlgebraicGeometry.GroupoidScheme.Hom H G'),
              IsOpenImmersion ι.obj.left ∧
                IsClosedImmersion ι.obj.left ∧
                IsOpenImmersion ι.arrow.left ∧
                IsClosedImmersion ι.arrow.left ∧
                IsFinite H.U.hom ∧
                IsFinite H.R.hom ∧
                ∃ u' : H.U.left,
                  H.U.hom u' = V.point ∧
                    (ι.obj.left ≫
                      (AlgebraicGeometry.GroupoidScheme.baseChangeProjection
                        V.toEtale.hom G).obj.left) u' = u ∧
                    H.U.hom ⁻¹' ({V.point} : Set V.toEtale.left) =
                      H.t.left '' (H.s.left ⁻¹' ({u'} : Set H.U.left)) ∧
                    H.R.hom ⁻¹' ({V.point} : Set V.toEtale.left) =
                      H.s.left ⁻¹'
                        (H.U.hom ⁻¹' ({V.point} : Set V.toEtale.left)))
