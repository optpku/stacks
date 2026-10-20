module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing

universe u

/- 81.13.3.1: the coequalizers of the infinitesimal-neighbourhood coproducts form
 the sequential system X_1 ⟶ X_2 ⟶ X_3 ⟶ ⋯ over X. -/
@[stacks 0AGJ] #check (AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.system :
    ∀ {S : Scheme.{u}} {X X' Z : AlgebraicSpace S}
      (f : X' ⟶ X) (i : Z ⟶ X),
      [IsLocallyNoetherian X] →
      [IsClosedImmersion i] →
      [Proper f] →
      IsIsoOverOpen f
        (closedImmersionComplementι i) →
      ℕ ⥤ AlgebraicSpace S)

section

variable {S : Scheme.{u}} {X X' Z : AlgebraicSpace S}
    (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X] [IsClosedImmersion i] [Proper f]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) (n : ℕ)

#check (AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.toAmbient f i h_iso n :
    stage f i n ⟶ X)
#check (AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.stageMap f i h_iso n :
    stage f i n ⟶ stage f i (n + 1))
#check (AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.cocone f i h_iso :
    Cocone (system f i h_iso))
#check (AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.stage_isCoequalizer f i h_iso n :
    ∀ (T : AlgebraicSpace S) (q : summand f i n ⟶ T),
      relationFst f i n ≫ q = relationSnd f i n ≫ q →
      ∃! d : stage f i n ⟶ T, fromSummand f i n ≫ d = q)
#check (AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.fromSummand_stageMap f i h_iso n :
    fromSummand f i n ≫ stageMap f i h_iso n =
      summandSucc f i n ≫ fromSummand f i (n + 1))
#check (AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.instUniversalHomeomorphism_stageMap
    f i h_iso n : UniversalHomeomorphism (stageMap f i h_iso n))
#check (AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.instUniversalHomeomorphism_toAmbient
    f i h_iso n : UniversalHomeomorphism (toAmbient f i h_iso n))

end
