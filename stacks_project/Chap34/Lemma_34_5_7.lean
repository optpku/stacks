module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.ChosenPresentation
import StacksCheckRecall

universe u v

/- Lemma 34.5.7 (1): every smooth cover of an object in a chosen big smooth
site is refined by the image of a covering family in the chosen carrier. -/
@[stacks 03WZ] #check
  (AlgebraicGeometry.ChosenBigSite.exists_coveringFamily_refining :
    ∀ (X : AlgebraicGeometry.ChosenBigSite.{u, v}
        AlgebraicGeometry.Scheme.bigSmoothPrecoverage) {T : X.carrier}
      (𝒰 : AlgebraicGeometry.Scheme.Cover.{u}
        AlgebraicGeometry.Scheme.bigSmoothPrecoverage (X.toScheme.obj T)),
      ∃ 𝒱 : CategoryTheory.Limits.FormalCoproduct.{u} (CategoryTheory.Over T),
        CategoryTheory.Limits.FormalCoproduct.Over.IsCovering
            (@CategoryTheory.Pretopology.toPrecoverage X.carrier
              (CategoryTheory.Cat.str X.carrier) X.hasPullbacks X.pretopology) 𝒱 ∧
          Nonempty
            (((CategoryTheory.Limits.FormalCoproduct.map
              (CategoryTheory.Over.post (X := T) X.toScheme)).obj 𝒱) ⟶
              CategoryTheory.Limits.FormalCoproduct.Over.ofArrows 𝒰.X 𝒰.f))

/- Lemma 34.5.7 (2): every standard smooth cover of an affine object in a
chosen big smooth site is tautologically equivalent to the image of a covering
family in the chosen carrier. -/
@[stacks 03WZ] #check
  (AlgebraicGeometry.ChosenBigSite.Smooth.exists_coveringFamily_tautologicallyEquivalent_standardSmoothCovering :
    ∀ (X : AlgebraicGeometry.ChosenBigSite.{u, v}
        AlgebraicGeometry.Scheme.bigSmoothPrecoverage) (T : X.carrier)
      [AlgebraicGeometry.IsAffine (X.toScheme.obj T)]
      (𝒰 : AlgebraicGeometry.StandardSmoothCovering (X.toScheme.obj T)),
      ∃ 𝒱 : CategoryTheory.Limits.FormalCoproduct.{u} (CategoryTheory.Over T),
        CategoryTheory.Limits.FormalCoproduct.Over.IsCovering
            (@CategoryTheory.Pretopology.toPrecoverage X.carrier
              (CategoryTheory.Cat.str X.carrier) X.hasPullbacks X.pretopology) 𝒱 ∧
          CategoryTheory.Limits.FormalCoproduct.TautologicallyEquivalent
            (CategoryTheory.Limits.FormalCoproduct.Over.ofArrows
              (fun j : ULift.{u} (Fin 𝒰.n) ↦ 𝒰.U j.down)
              (fun j : ULift.{u} (Fin 𝒰.n) ↦ 𝒰.map j.down))
            ((CategoryTheory.Limits.FormalCoproduct.map
              (CategoryTheory.Over.post (X := T) X.toScheme)).obj 𝒱))

/- Lemma 34.5.7 (3): every Zariski open cover of an object in a chosen big
smooth site is tautologically equivalent to the image of a covering family in
the chosen carrier. -/
@[stacks 03WZ] #check
  (AlgebraicGeometry.ChosenBigSite.Smooth.exists_coveringFamily_tautologicallyEquivalent_zariskiCover :
    ∀ (X : AlgebraicGeometry.ChosenBigSite.{u, v}
        AlgebraicGeometry.Scheme.bigSmoothPrecoverage) (T : X.carrier)
      (𝒰 : (X.toScheme.obj T).OpenCover.{u}),
      ∃ 𝒱 : CategoryTheory.Limits.FormalCoproduct.{u} (CategoryTheory.Over T),
        CategoryTheory.Limits.FormalCoproduct.Over.IsCovering
            (@CategoryTheory.Pretopology.toPrecoverage X.carrier
              (CategoryTheory.Cat.str X.carrier) X.hasPullbacks X.pretopology) 𝒱 ∧
          CategoryTheory.Limits.FormalCoproduct.TautologicallyEquivalent
            (CategoryTheory.Limits.FormalCoproduct.Over.ofArrows 𝒰.X 𝒰.f)
            ((CategoryTheory.Limits.FormalCoproduct.map
              (CategoryTheory.Over.post (X := T) X.toScheme)).obj 𝒱))
