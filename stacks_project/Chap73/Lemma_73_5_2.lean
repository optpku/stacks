/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Smooth.Comparison

/-!
# Étale and Zariski coverings are smooth coverings

Every étale covering family of algebraic spaces over a scheme `S` is a smooth
covering family, and therefore every Zariski covering family is a smooth covering
family.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 73.5.2: any étale covering is a smooth covering. -/
@[stacks 0DFA] #check (AlgebraicGeometry.AlgebraicSpace.smoothCovering_of_etaleCovering :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    {family : ι → Over X},
    EtaleCovering family → SmoothCovering family)

/- Lemma 73.5.2: any Zariski covering is a smooth covering. -/
@[stacks 0DFA] #check (AlgebraicGeometry.AlgebraicSpace.smoothCovering_of_zariskiPrecoverage :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    {Xᵢ : ι → AlgebraicSpace S} {f : ∀ i, Xᵢ i ⟶ X},
    Presieve.ofArrows Xᵢ f ∈ zariskiPrecoverage S X →
      SmoothCovering (fun i ↦ Over.mk (f i)))

/- An indexed family that belongs to `etalePrecoverage` is a `SmoothCovering`
after presentation as an `Over` family. -/
#check (AlgebraicGeometry.AlgebraicSpace.smoothCovering_of_mem_etalePrecoverage :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    {Xᵢ : ι → AlgebraicSpace S} {f : ∀ i, Xᵢ i ⟶ X},
    Presieve.ofArrows Xᵢ f ∈ etalePrecoverage X →
      SmoothCovering (fun i ↦ Over.mk (f i)))

end AlgebraicGeometry.AlgebraicSpace
