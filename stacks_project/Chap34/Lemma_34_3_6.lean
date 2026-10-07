module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Covering
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 34.3.6: every Zariski covering of the scheme underlying an object of a chosen big
Zariski site is tautologically equivalent to the image of a covering family in that site. -/
@[stacks 03WV] #check
  (AlgebraicGeometry.ChosenBigSite.exists_coveringFamily_tautologicallyEquivalent
    (P := AlgebraicGeometry.Scheme.zariskiPrecoverage) :
    ∀ (X : AlgebraicGeometry.ChosenBigZariskiSite.{u, v}) {T : X.carrier},
      (𝒰 : (X.toScheme.obj T).OpenCover.{u}) →
        ∃ 𝒱 : CategoryTheory.Limits.FormalCoproduct.{u} (CategoryTheory.Over T),
          CategoryTheory.Limits.FormalCoproduct.Over.IsCovering
              (@CategoryTheory.Pretopology.toPrecoverage X.carrier
                (CategoryTheory.Cat.str X.carrier) X.hasPullbacks X.pretopology) 𝒱 ∧
            CategoryTheory.Limits.FormalCoproduct.TautologicallyEquivalent
              ((CategoryTheory.Limits.FormalCoproduct.map
                (CategoryTheory.Over.post (X := T) X.toScheme)).obj 𝒱)
              (CategoryTheory.Limits.FormalCoproduct.Over.ofArrows 𝒰.X 𝒰.f))
