module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ChosenPresentation

universe u v

/- Lemma 34.4.7 (1): every étale covering of an object in a chosen big étale
site is refined by a covering family in that chosen site. -/
@[stacks 03WW] #check
  (AlgebraicGeometry.ChosenBigSite.exists_coveringFamily_refining :
    ∀ (X : AlgebraicGeometry.ChosenBigSite.{u, v}
        AlgebraicGeometry.Scheme.etalePrecoverage) {T : X.carrier}
      (𝒰 : AlgebraicGeometry.Scheme.Cover.{u}
        AlgebraicGeometry.Scheme.etalePrecoverage (X.toScheme.obj T)),
      ∃ 𝒱 : CategoryTheory.Limits.FormalCoproduct.{u} (CategoryTheory.Over T),
        CategoryTheory.Limits.FormalCoproduct.IsCovering
            (@CategoryTheory.Pretopology.toPrecoverage X.carrier
              (CategoryTheory.Cat.str X.carrier) X.hasPullbacks X.pretopology) 𝒱 ∧
          Nonempty
            (((CategoryTheory.Limits.FormalCoproduct.map
              (CategoryTheory.Over.post (X := T) X.toScheme)).obj 𝒱) ⟶
              CategoryTheory.Limits.FormalCoproduct.ofArrows 𝒰.X 𝒰.f))

/- Lemma 34.4.7 (2): a standard étale covering is tautologically equivalent
to a covering family in the chosen big étale site. -/
@[stacks 03WW] #check
  (AlgebraicGeometry.ChosenBigSite.exists_coveringFamily_tautologicallyEquivalent_standardEtaleCover :
    ∀ (X : AlgebraicGeometry.ChosenBigSite.{u, v}
        AlgebraicGeometry.Scheme.etalePrecoverage) (T : X.carrier)
      [AlgebraicGeometry.IsAffine (X.toScheme.obj T)]
      (𝒰 : AlgebraicGeometry.StandardEtaleCover (X.toScheme.obj T)),
      ∃ 𝒱 : CategoryTheory.Limits.FormalCoproduct.{u} (CategoryTheory.Over T),
        CategoryTheory.Limits.FormalCoproduct.IsCovering
            (@CategoryTheory.Pretopology.toPrecoverage X.carrier
              (CategoryTheory.Cat.str X.carrier) X.hasPullbacks X.pretopology) 𝒱 ∧
          CategoryTheory.Limits.FormalCoproduct.TautologicallyEquivalent
            (CategoryTheory.Limits.FormalCoproduct.ofArrows
              (fun j : ULift.{u} (Fin 𝒰.n) ↦ 𝒰.U j.down)
              (fun j : ULift.{u} (Fin 𝒰.n) ↦ 𝒰.map j.down))
            ((CategoryTheory.Limits.FormalCoproduct.map
              (CategoryTheory.Over.post (X := T) X.toScheme)).obj 𝒱))

/- Lemma 34.4.7 (3): a Zariski open covering is tautologically equivalent to
a covering family in the chosen big étale site. -/
@[stacks 03WW] #check
  (AlgebraicGeometry.ChosenBigSite.Etale.exists_coveringFamily_tautologicallyEquivalent_zariskiCover :
    ∀ (X : AlgebraicGeometry.ChosenBigSite.{u, v}
        AlgebraicGeometry.Scheme.etalePrecoverage) (T : X.carrier)
      (𝒰 : (X.toScheme.obj T).OpenCover.{u}),
      ∃ 𝒱 : CategoryTheory.Limits.FormalCoproduct.{u} (CategoryTheory.Over T),
        CategoryTheory.Limits.FormalCoproduct.IsCovering
            (@CategoryTheory.Pretopology.toPrecoverage X.carrier
              (CategoryTheory.Cat.str X.carrier) X.hasPullbacks X.pretopology) 𝒱 ∧
          CategoryTheory.Limits.FormalCoproduct.TautologicallyEquivalent
            (CategoryTheory.Limits.FormalCoproduct.ofArrows 𝒰.X 𝒰.f)
            ((CategoryTheory.Limits.FormalCoproduct.map
              (CategoryTheory.Over.post (X := T) X.toScheme)).obj 𝒱))
