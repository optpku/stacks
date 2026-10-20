/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Covering

/-!
# Covering families in chosen big h sites

This module compares h, standard h, and Zariski covering families with
covering families in an explicit chosen big h-site presentation.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigHSite

variable (Schh : ChosenBigHSite.{u, v}) {T : Schh.carrier}

/-- Every h covering of the scheme underlying an object in a chosen big h site
is refined by a covering family in the chosen carrier. -/
theorem refineHCovering {ι : Type u}
    (family : ι → Over (Schh.toScheme.obj T))
    (hfamily : Scheme.HCovering family) :
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
      Limits.FormalCoproduct.IsCovering
          (@Pretopology.toPrecoverage Schh.carrier (Cat.str Schh.carrier)
            Schh.hasPullbacks Schh.pretopology) 𝒱 ∧
        Nonempty
          (((Limits.FormalCoproduct.map
            (Over.post Schh.toScheme)).obj 𝒱) ⟶
            Limits.FormalCoproduct.ofArrows
              (fun i ↦ (family i).left) (fun i ↦ (family i).hom)) := sorry

/-- Every finite affine h covering of the affine scheme underlying an object
in a chosen big h site is tautologically equivalent to a covering family in
the chosen carrier. -/
theorem realizeStandard [IsAffine (Schh.toScheme.obj T)]
    (family : AffineFamilyOver (Schh.toScheme.obj T))
    (hfamily : Scheme.HCovering (fun i : Fin family.n ↦ Over.mk (family.map i))) :
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
      Limits.FormalCoproduct.IsCovering
          (@Pretopology.toPrecoverage Schh.carrier (Cat.str Schh.carrier)
            Schh.hasPullbacks Schh.pretopology) 𝒱 ∧
        Limits.FormalCoproduct.TautologicallyEquivalent
          (Limits.FormalCoproduct.ofArrows
            (fun j : ULift.{u} (Fin family.n) ↦ family.U j.down)
            (fun j : ULift.{u} (Fin family.n) ↦ family.map j.down))
          ((Limits.FormalCoproduct.map
            (Over.post Schh.toScheme)).obj 𝒱) := sorry

/-- Every Zariski open covering of the scheme underlying an object in a chosen
big h site is tautologically equivalent to a covering family in the chosen
carrier. -/
theorem realizeZariski (𝒰 : (Schh.toScheme.obj T).OpenCover.{u}) :
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
      Limits.FormalCoproduct.IsCovering
          (@Pretopology.toPrecoverage Schh.carrier (Cat.str Schh.carrier)
            Schh.hasPullbacks Schh.pretopology) 𝒱 ∧
        Limits.FormalCoproduct.TautologicallyEquivalent
          (Limits.FormalCoproduct.ofArrows 𝒰.X 𝒰.f)
          ((Limits.FormalCoproduct.map
            (Over.post Schh.toScheme)).obj 𝒱) := sorry

end AlgebraicGeometry.ChosenBigHSite
