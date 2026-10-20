/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 33.44.3: let `k` be a field, let `X` be a proper scheme of dimension `≤ 1` over `k`,
and let `0 → 𝓔₁ → 𝓔₂ → 𝓔₃ → 0` be a short exact sequence of locally free `𝒪_X`-modules each of
finite constant rank. Then `deg (𝓔₂) = deg (𝓔₁) + deg (𝓔₃)`. -/
@[stacks 0AYS] #check
  (AlgebraicGeometry.Scheme.Modules.curveDegree_eq_add_of_shortExact_of_properOverField :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}} {S : ShortComplex X.Modules}
      {n₁ n₂ n₃ : ℕ} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (hdim : topologicalKrullDim X ≤ 1)
      [IsFiniteLocallyFreeOfRank n₁ S.X₁]
      [IsFiniteLocallyFreeOfRank n₂ S.X₂]
      [IsFiniteLocallyFreeOfRank n₃ S.X₃],
      S.ShortExact →
        curveDegree f hdim S.X₂ n₂ =
          curveDegree f hdim S.X₁ n₁ + curveDegree f hdim S.X₃ n₃)

end AlgebraicGeometry.Scheme.Modules
