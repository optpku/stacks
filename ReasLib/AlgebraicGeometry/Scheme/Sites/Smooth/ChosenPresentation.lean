/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Covering
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardSmooth

/-!
# Smooth covers in chosen big-site presentations

Standard smooth and Zariski covering families can be represented by covering
families in a chosen big smooth site.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigSite.Smooth

variable (X : ChosenBigSite.{u, v} Scheme.bigSmoothPrecoverage) (T : X.carrier)

/-- Every standard smooth cover of the underlying affine scheme of a chosen-site
object is tautologically equivalent to the image of a covering family in the
chosen smooth carrier. -/
theorem exists_coveringFamily_tautologicallyEquivalent_standardSmoothCovering
    [IsAffine (X.toScheme.obj T)]
    (𝒰 : StandardSmoothCovering (X.toScheme.obj T)) :
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
      Limits.FormalCoproduct.IsCovering
          (@Pretopology.toPrecoverage X.carrier (Cat.str X.carrier)
            X.hasPullbacks X.pretopology) 𝒱 ∧
        Limits.FormalCoproduct.TautologicallyEquivalent
          (Limits.FormalCoproduct.ofArrows
            (fun j : ULift.{u} (Fin 𝒰.n) ↦ 𝒰.U j.down)
            (fun j : ULift.{u} (Fin 𝒰.n) ↦ 𝒰.map j.down))
          ((Limits.FormalCoproduct.map (Over.post (X := T) X.toScheme)).obj 𝒱) := sorry

/-- Every Zariski open cover of the underlying scheme of a chosen-site object
is tautologically equivalent to the image of a covering family in the chosen
smooth carrier. -/
theorem exists_coveringFamily_tautologicallyEquivalent_zariskiCover
    (𝒰 : (X.toScheme.obj T).OpenCover.{u}) :
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
      Limits.FormalCoproduct.IsCovering
          (@Pretopology.toPrecoverage X.carrier (Cat.str X.carrier)
            X.hasPullbacks X.pretopology) 𝒱 ∧
        Limits.FormalCoproduct.TautologicallyEquivalent
          (Limits.FormalCoproduct.ofArrows 𝒰.X 𝒰.f)
          ((Limits.FormalCoproduct.map (Over.post (X := T) X.toScheme)).obj 𝒱) := sorry

end AlgebraicGeometry.ChosenBigSite.Smooth
