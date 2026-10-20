module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Splitting.EtaleLocalization
public import stacks_project.Chap79.Situation_79_15_3_Splitting
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 79.15.6 (Existence of splitting): an étale localization of a groupoid
scheme satisfying the splitting hypotheses is split over a residue-field point
above the chosen object point. -/
@[stacks 0DTC] #check (AlgebraicGeometry.GroupoidScheme.exists_etale_isSplitOver :
  ∀ {S : Scheme.{u}} (G : GroupoidScheme S) (u : G.U.left)
    [IsSplittingSituation G u],
    ∃ (U' : AlgebraicSpace S) (g : U' ⟶ ofOver G.U)
      (u' : ofOver (residueOver G u) ⟶ U'),
      AlgebraicSpace.Etale g ∧
        u' ≫ g = residueMap G u ∧
          GroupoidAlgebraicSpace.IsSplitOver
            (GroupoidAlgebraicSpace.pullback (GroupoidAlgebraicSpace.ofScheme G)
              (objectRestrictionHom G g))
            (residueFieldPoint G u u'))

end AlgebraicGeometry.GroupoidScheme
