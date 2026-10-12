/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic.ChosenPresentation
import StacksCheckRecall

open CategoryTheory

universe u v

/- Lemma 34.6.7 (1): every syntomic cover of an object in a chosen big syntomic
site is refined by the image of a covering family in the chosen carrier. -/
@[stacks 03X2] #check
  (AlgebraicGeometry.ChosenBigSite.exists_coveringFamily_refining_syntomicCover :
    ∀ (X : AlgebraicGeometry.ChosenBigSite.{u, v}
        (AlgebraicGeometry.Scheme.precoverage (@AlgebraicGeometry.Syntomic)))
      {T : X.carrier} (𝒰 : AlgebraicGeometry.SyntomicCover.{u, u} (X.toScheme.obj T)),
      ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
        Limits.FormalCoproduct.Over.IsCovering
            (@Pretopology.toPrecoverage X.carrier (Cat.str X.carrier)
              X.hasPullbacks X.pretopology) 𝒱 ∧
          Nonempty
            (((Limits.FormalCoproduct.map (Over.post (X := T) X.toScheme)).obj 𝒱) ⟶
              Limits.FormalCoproduct.Over.ofArrows 𝒰.X 𝒰.f))

/- Lemma 34.6.7 (2): every standard syntomic cover of an affine object in a
chosen big syntomic site is tautologically equivalent to the image of a
covering family in the chosen carrier. -/
@[stacks 03X2] #check
  (AlgebraicGeometry.ChosenBigSite.exists_coveringFamily_tautologicallyEquivalent_standardSyntomicCovering :
    ∀ (X : AlgebraicGeometry.ChosenBigSite.{u, v}
        (AlgebraicGeometry.Scheme.precoverage (@AlgebraicGeometry.Syntomic)))
      {T : X.carrier} [AlgebraicGeometry.IsAffine (X.toScheme.obj T)]
      (𝒰 : AlgebraicGeometry.StandardSyntomicCovering (X.toScheme.obj T)),
      ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
        Limits.FormalCoproduct.Over.IsCovering
            (@Pretopology.toPrecoverage X.carrier (Cat.str X.carrier)
              X.hasPullbacks X.pretopology) 𝒱 ∧
          Limits.FormalCoproduct.TautologicallyEquivalent
            (Limits.FormalCoproduct.Over.ofArrows
              (fun j : ULift.{u} (Fin 𝒰.n) ↦ 𝒰.U j.down)
              (fun j : ULift.{u} (Fin 𝒰.n) ↦ 𝒰.map j.down))
            ((Limits.FormalCoproduct.map (Over.post (X := T) X.toScheme)).obj 𝒱))

/- Lemma 34.6.7 (3): every Zariski open cover of an object in a chosen big
syntomic site is tautologically equivalent to the image of a covering family
in the chosen carrier. -/
@[stacks 03X2] #check
  (AlgebraicGeometry.ChosenBigSite.exists_coveringFamily_tautologicallyEquivalent_zariskiCover :
    ∀ (X : AlgebraicGeometry.ChosenBigSite.{u, v}
        (AlgebraicGeometry.Scheme.precoverage (@AlgebraicGeometry.Syntomic)))
      {T : X.carrier} (𝒰 : (X.toScheme.obj T).OpenCover.{u}),
      ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
        Limits.FormalCoproduct.Over.IsCovering
            (@Pretopology.toPrecoverage X.carrier (Cat.str X.carrier)
              X.hasPullbacks X.pretopology) 𝒱 ∧
          Limits.FormalCoproduct.TautologicallyEquivalent
            (Limits.FormalCoproduct.Over.ofArrows 𝒰.X 𝒰.f)
            ((Limits.FormalCoproduct.map (Over.post (X := T) X.toScheme)).obj 𝒱))
