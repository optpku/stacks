/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AffineCover
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory.Limits
open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.AffineOpenCover

/- Lemma 30.4.4: let `X` be a quasi-compact quasi-separated scheme covered by finitely many
quasi-compact separated opens. Then cohomology of every quasi-coherent module vanishes in degrees
at least `max_I (|I| + t(⋂ i ∈ I, U i) - 1)`, where `t` is the minimal affine-cover number. -/
@[stacks 071L] #check (globalCohomology_isZero_of_finiteCover :
  ∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    {m : ℕ} (U : Fin m → X.Opens) (hcover : IsOpenCover U)
    (hUcompact : ∀ i, CompactSpace (U i : Scheme))
    (hUseparated : ∀ i, (U i : Scheme).IsSeparated)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (p : ℕ), cohomologyBound U ≤ p →
      IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' p (⊤ : Opens X)))

#check (cohomologyBound :
  ∀ {X : Scheme.{u}} {m : ℕ} (U : Fin m → X.Opens), ℕ)

end AlgebraicGeometry.Scheme.AffineOpenCover
