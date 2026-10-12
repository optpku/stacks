/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Covering
public import stacks_project.Chap61.Definition_61_12_8_Presentation
import StacksCheckRecall

universe u v

/- Lemma 61.31.1: for a big pro-étale site Sch_proétale as in
Definition 61.12.7 and T in that site, every ambient pro-étale covering
{T_i ⟶ T} is refined by some covering {U_j ⟶ T} that lies in the site. -/
@[stacks 098J] #check
  (AlgebraicGeometry.ChosenBigSite.exists_coveringFamily_refining :
    ∀ (X : AlgebraicGeometry.ChosenBigProetaleSite.{u, v}) {T : X.carrier}
      (𝒰 : AlgebraicGeometry.Scheme.Cover.{u}
        AlgebraicGeometry.Scheme.proetalePrecoverage (X.toScheme.obj T)),
      ∃ 𝒱 : CategoryTheory.Limits.FormalCoproduct.{u} (CategoryTheory.Over T),
        CategoryTheory.Limits.FormalCoproduct.Over.IsCovering
            (@CategoryTheory.Pretopology.toPrecoverage X.carrier
              (CategoryTheory.Cat.str X.carrier) X.hasPullbacks X.pretopology) 𝒱 ∧
          Nonempty
            (((CategoryTheory.Limits.FormalCoproduct.map
              (CategoryTheory.Over.post (X := T) X.toScheme)).obj 𝒱) ⟶
              CategoryTheory.Limits.FormalCoproduct.Over.ofArrows 𝒰.X 𝒰.f))
