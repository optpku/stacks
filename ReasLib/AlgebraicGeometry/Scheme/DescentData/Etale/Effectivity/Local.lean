/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale.Effectivity
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale.Pullback

/-!
# Local effectivity of étale descent data

Effectivity of an étale descent datum can be checked on an open cover when the canonical
functors on pairwise intersections are fully faithful and those on triple intersections
are faithful.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.DescentData.Etale.IsEffective

/-- An étale descent datum effective over an open cover is effective globally when the
restricted canonical functors are fully faithful on pairwise intersections and faithful
on triple intersections. -/
theorem ofOpenCover {X S : Scheme.{u}} (f : X ⟶ S) (D : Etale f)
    {ι : Type v} (U : ι → S.Opens) (hU : TopologicalSpace.IsOpenCover U)
    (h_effective : ∀ i, ((baseChangeFunctor f (U i).ι).obj D).IsEffective)
    (h_fullyFaithful : ∀ i j,
      Nonempty (canonicalFunctor (pullback.snd f (U i ⊓ U j).ι)).FullyFaithful)
    (h_faithful : ∀ i j k,
      (canonicalFunctor (pullback.snd f (U i ⊓ U j ⊓ U k).ι)).Faithful) :
    D.IsEffective := sorry

end AlgebraicGeometry.Scheme.DescentData.Etale.IsEffective
