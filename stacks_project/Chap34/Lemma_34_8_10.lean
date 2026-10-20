/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.ChosenCovering

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

/- Lemma 34.8.10 (1): every `ph` covering of the scheme underlying an object
of a big `ph` site admits a refinement by a covering family in the site. -/
@[stacks 0DBK] #check
  (AlgebraicGeometry.ChosenBigPhSite.exists_coveringFamily_refining_phCovering :
    ∀ (Schph : ChosenBigPhSite.{u, v}) {T : Schph.carrier}
      {ι : Type u} (X : ι → Scheme.{u}) (π : ∀ i, X i ⟶ Schph.toScheme.obj T),
      PhCovering X π →
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
      Limits.FormalCoproduct.IsCovering
          (@Pretopology.toPrecoverage Schph.carrier (Cat.str Schph.carrier)
            Schph.hasPullbacks Schph.pretopology) 𝒱 ∧
        Nonempty
          (((Limits.FormalCoproduct.map
            (Over.post (X := T) Schph.toScheme)).obj 𝒱) ⟶
            Limits.FormalCoproduct.ofArrows X π))

/- Lemma 34.8.10 (2): a standard `ph` covering of the affine scheme underlying
an object of a big `ph` site is tautologically equivalent to a covering family
in the site. -/
@[stacks 0DBK] #check
  (AlgebraicGeometry.ChosenBigPhSite.exists_coveringFamily_tautologicallyEquivalent_standardPhCovering :
    ∀ (Schph : ChosenBigPhSite.{u, v}) {T : Schph.carrier}
      [IsAffine (Schph.toScheme.obj T)]
      (𝒰₀ : StandardPhCovering (Schph.toScheme.obj T)),
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
      Limits.FormalCoproduct.IsCovering
          (@Pretopology.toPrecoverage Schph.carrier (Cat.str Schph.carrier)
            Schph.hasPullbacks Schph.pretopology) 𝒱 ∧
        Limits.FormalCoproduct.TautologicallyEquivalent
          (Limits.FormalCoproduct.ofArrows
            (fun j : ULift.{u} (Fin 𝒰₀.m) ↦ 𝒰₀.obj j.down)
            (fun j : ULift.{u} (Fin 𝒰₀.m) ↦ 𝒰₀.map j.down))
          ((Limits.FormalCoproduct.map
            (Over.post (X := T) Schph.toScheme)).obj 𝒱))

/- Lemma 34.8.10 (3): a Zariski covering of the scheme underlying an object of
a big `ph` site is tautologically equivalent to a covering family in the site. -/
@[stacks 0DBK] #check
  (AlgebraicGeometry.ChosenBigPhSite.exists_coveringFamily_tautologicallyEquivalent_zariskiCover :
    ∀ (Schph : ChosenBigPhSite.{u, v}) {T : Schph.carrier}
      (𝒰₀ : (Schph.toScheme.obj T).OpenCover.{u}),
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
      Limits.FormalCoproduct.IsCovering
          (@Pretopology.toPrecoverage Schph.carrier (Cat.str Schph.carrier)
            Schph.hasPullbacks Schph.pretopology) 𝒱 ∧
        Limits.FormalCoproduct.TautologicallyEquivalent
          (Limits.FormalCoproduct.ofArrows 𝒰₀.X 𝒰₀.f)
          ((Limits.FormalCoproduct.map
            (Over.post (X := T) Schph.toScheme)).obj 𝒱))
