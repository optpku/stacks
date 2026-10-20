module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.ChosenCovering
import StacksCheckRecall

open CategoryTheory

universe u v

/- Lemma 34.7.7 (1): every fppf cover of an object in a chosen big fppf site
is refined by the image of a covering family in the chosen carrier. -/
@[stacks 03WX] #check
  (AlgebraicGeometry.ChosenBigSite.exists_coveringFamily_refining :
    ∀ (X : AlgebraicGeometry.ChosenBigSite.{u, v}
        AlgebraicGeometry.Scheme.fppfPrecoverage)
      {T : X.carrier}
      (𝒰 : AlgebraicGeometry.Scheme.Cover.{u}
        AlgebraicGeometry.Scheme.fppfPrecoverage (X.toScheme.obj T)),
      ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
        Limits.FormalCoproduct.IsCovering
            (@Pretopology.toPrecoverage X.carrier (Cat.str X.carrier)
              X.hasPullbacks X.pretopology) 𝒱 ∧
          Nonempty
            (((Limits.FormalCoproduct.map (Over.post (X := T) X.toScheme)).obj 𝒱) ⟶
              Limits.FormalCoproduct.ofArrows 𝒰.X 𝒰.f))

/- Lemma 34.7.7 (2): every standard fppf cover of an affine object in a chosen
big fppf site is tautologically equivalent to the image of a covering family
in the chosen carrier. -/
@[stacks 03WX] #check
  (AlgebraicGeometry.ChosenBigSite.Fppf.exists_coveringFamily_tautologicallyEquivalent_standardCover :
    ∀ (X : AlgebraicGeometry.ChosenBigSite.{u, v}
        AlgebraicGeometry.Scheme.fppfPrecoverage)
      (T : X.carrier) [AlgebraicGeometry.IsAffine (X.toScheme.obj T)]
      (𝒰 : AlgebraicGeometry.StandardFppfCover (X.toScheme.obj T)),
      ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
        Limits.FormalCoproduct.IsCovering
            (@Pretopology.toPrecoverage X.carrier (Cat.str X.carrier)
              X.hasPullbacks X.pretopology) 𝒱 ∧
          Limits.FormalCoproduct.TautologicallyEquivalent
            (Limits.FormalCoproduct.ofArrows
              (fun j : ULift.{u} (Fin 𝒰.n) ↦ 𝒰.U j.down)
              (fun j : ULift.{u} (Fin 𝒰.n) ↦ 𝒰.map j.down))
            ((Limits.FormalCoproduct.map (Over.post (X := T) X.toScheme)).obj 𝒱))

/- Lemma 34.7.7 (3): every Zariski open cover of an object in a chosen big
fppf site is tautologically equivalent to the image of a covering family in
the chosen carrier. -/
@[stacks 03WX] #check
  (AlgebraicGeometry.ChosenBigSite.Fppf.exists_coveringFamily_tautologicallyEquivalent_zariskiCover :
    ∀ (X : AlgebraicGeometry.ChosenBigSite.{u, v}
        AlgebraicGeometry.Scheme.fppfPrecoverage)
      (T : X.carrier) (𝒰 : (X.toScheme.obj T).OpenCover.{u}),
      ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
        Limits.FormalCoproduct.IsCovering
            (@Pretopology.toPrecoverage X.carrier (Cat.str X.carrier)
              X.hasPullbacks X.pretopology) 𝒱 ∧
          Limits.FormalCoproduct.TautologicallyEquivalent
            (Limits.FormalCoproduct.ofArrows 𝒰.X 𝒰.f)
            ((Limits.FormalCoproduct.map (Over.post (X := T) X.toScheme)).obj 𝒱))
