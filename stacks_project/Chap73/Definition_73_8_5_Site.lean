/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PhPrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PhPrecoverage.ChosenSite

/-!
# Chosen big ph sites of algebraic spaces

The shared ph precoverage and chosen-site specialization are checked here for
source-facing consumers of this module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (phPrecoverage : ∀ {S : Scheme.{u}}, Precoverage (AlgebraicSpace S))

#check (mem_phPrecoverage_iff :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {R : Presieve X},
      R ∈ phPrecoverage X ↔
      ∃ (ι : Type (u + 1)) (Y : ι → AlgebraicSpace S) (f : ∀ i, Y i ⟶ X),
        R = Presieve.ofArrows Y f ∧ PhCovering Y f)

#check (ofArrows_mem_phPrecoverage_iff :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {ι : Type (u + 1)} {Y : ι → AlgebraicSpace S} (f : ∀ i, Y i ⟶ X),
      Presieve.ofArrows Y f ∈ phPrecoverage X ↔ PhCovering Y f)

#check (phPrecoverage.instIsSite : ∀ {S : Scheme.{u}},
    (phPrecoverage : Precoverage (AlgebraicSpace S)).IsSite)

#check (ChosenBigPhSite : Scheme.{u} → Type (u + 2))

#check (ChosenBigPhSite.exists : ∀ S : Scheme.{u}, Nonempty (ChosenBigPhSite S))

end AlgebraicGeometry.AlgebraicSpace
