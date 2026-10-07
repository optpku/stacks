module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.H.ChosenCovering

open CategoryTheory

universe u v

/- Lemma 38.34.12 (1): every h covering of the scheme underlying an object of
a big h site admits a refinement by a covering family in the site. -/
@[stacks 0EU0] #check (AlgebraicGeometry.ChosenBigHSite.refineHCovering :
  ∀ (Schh : AlgebraicGeometry.ChosenBigHSite.{u, v}) {T : Schh.carrier}
    {ι : Type u} (family : ι → Over (Schh.toScheme.obj T)),
    AlgebraicGeometry.Scheme.HCovering family →
      ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
        Limits.FormalCoproduct.Over.IsCovering
            (@Pretopology.toPrecoverage Schh.carrier (Cat.str Schh.carrier)
              Schh.hasPullbacks Schh.pretopology) 𝒱 ∧
          Nonempty
            (((Limits.FormalCoproduct.map
              (Over.post Schh.toScheme)).obj 𝒱) ⟶
              Limits.FormalCoproduct.Over.ofArrows
                (fun i ↦ (family i).left) (fun i ↦ (family i).hom)))

/- Lemma 38.34.12 (2): every standard h covering of an affine object of a big
h site is tautologically equivalent to a covering family in the site. -/
@[stacks 0EU0] #check (AlgebraicGeometry.ChosenBigHSite.realizeStandard :
  ∀ (Schh : AlgebraicGeometry.ChosenBigHSite.{u, v}) {T : Schh.carrier}
    [AlgebraicGeometry.IsAffine (Schh.toScheme.obj T)]
    (family : AlgebraicGeometry.AffineFamilyOver (Schh.toScheme.obj T)),
    AlgebraicGeometry.Scheme.HCovering
        (fun i : Fin family.n ↦ Over.mk (family.map i)) →
      ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
        Limits.FormalCoproduct.Over.IsCovering
            (@Pretopology.toPrecoverage Schh.carrier (Cat.str Schh.carrier)
              Schh.hasPullbacks Schh.pretopology) 𝒱 ∧
          Limits.FormalCoproduct.TautologicallyEquivalent
            (Limits.FormalCoproduct.Over.ofArrows
              (fun j : ULift.{u} (Fin family.n) ↦ family.U j.down)
              (fun j : ULift.{u} (Fin family.n) ↦ family.map j.down))
            ((Limits.FormalCoproduct.map
              (Over.post Schh.toScheme)).obj 𝒱))

/- Lemma 38.34.12 (3): every Zariski covering of an object of a big h site is
tautologically equivalent to a covering family in the site. -/
@[stacks 0EU0] #check (AlgebraicGeometry.ChosenBigHSite.realizeZariski :
  ∀ (Schh : AlgebraicGeometry.ChosenBigHSite.{u, v}) {T : Schh.carrier}
    (𝒰 : (Schh.toScheme.obj T).OpenCover.{u}),
      ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
        Limits.FormalCoproduct.Over.IsCovering
            (@Pretopology.toPrecoverage Schh.carrier (Cat.str Schh.carrier)
              Schh.hasPullbacks Schh.pretopology) 𝒱 ∧
          Limits.FormalCoproduct.TautologicallyEquivalent
            (Limits.FormalCoproduct.Over.ofArrows 𝒰.X 𝒰.f)
            ((Limits.FormalCoproduct.map
              (Over.post Schh.toScheme)).obj 𝒱))
