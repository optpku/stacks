/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.ChosenCovering

@[expose] public section

open CategoryTheory

universe u v

/- Every h covering of the scheme underlying an object in a chosen big h site
is refined by a covering family in the chosen carrier. -/
#check (AlgebraicGeometry.ChosenBigHSite.refineHCovering :
  ∀ (Schh : AlgebraicGeometry.ChosenBigHSite.{u, v}) {T : Schh.carrier}
    {ι : Type u} (family : ι → Over (Schh.toScheme.obj T)),
    AlgebraicGeometry.Scheme.HCovering family →
      ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
        Limits.FormalCoproduct.IsCovering
            (@Pretopology.toPrecoverage Schh.carrier (Cat.str Schh.carrier)
              Schh.hasPullbacks Schh.pretopology) 𝒱 ∧
          Nonempty
            (((Limits.FormalCoproduct.map
              (Over.post Schh.toScheme)).obj 𝒱) ⟶
              Limits.FormalCoproduct.ofArrows
                (fun i ↦ (family i).left) (fun i ↦ (family i).hom)))

/- Every finite affine h covering of the affine scheme underlying an object
in a chosen big h site is tautologically equivalent to a covering family in
the chosen carrier. -/
#check (AlgebraicGeometry.ChosenBigHSite.realizeStandard :
  ∀ (Schh : AlgebraicGeometry.ChosenBigHSite.{u, v}) {T : Schh.carrier}
    [AlgebraicGeometry.IsAffine (Schh.toScheme.obj T)]
    (family : AlgebraicGeometry.AffineFamilyOver (Schh.toScheme.obj T)),
    AlgebraicGeometry.Scheme.HCovering
        (fun i : Fin family.n ↦ Over.mk (family.map i)) →
      ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
        Limits.FormalCoproduct.IsCovering
            (@Pretopology.toPrecoverage Schh.carrier (Cat.str Schh.carrier)
              Schh.hasPullbacks Schh.pretopology) 𝒱 ∧
          Limits.FormalCoproduct.TautologicallyEquivalent
            (Limits.FormalCoproduct.ofArrows
              (fun j : ULift.{u} (Fin family.n) ↦ family.U j.down)
              (fun j : ULift.{u} (Fin family.n) ↦ family.map j.down))
            ((Limits.FormalCoproduct.map
              (Over.post Schh.toScheme)).obj 𝒱))

/- Every Zariski open covering of the scheme underlying an object in a chosen
big h site is tautologically equivalent to a covering family in the chosen
carrier. -/
#check (AlgebraicGeometry.ChosenBigHSite.realizeZariski :
  ∀ (Schh : AlgebraicGeometry.ChosenBigHSite.{u, v}) {T : Schh.carrier}
    (𝒰 : (Schh.toScheme.obj T).OpenCover.{u}),
      ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
        Limits.FormalCoproduct.IsCovering
            (@Pretopology.toPrecoverage Schh.carrier (Cat.str Schh.carrier)
              Schh.hasPullbacks Schh.pretopology) 𝒱 ∧
          Limits.FormalCoproduct.TautologicallyEquivalent
            (Limits.FormalCoproduct.ofArrows 𝒰.X 𝒰.f)
            ((Limits.FormalCoproduct.map
              (Over.post Schh.toScheme)).obj 𝒱))
