/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Frobenius.FiniteField
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.SchemeOverField

universe u v w

/- Lemma 64.3.5 (1): for a sheaf F on X_étale there is a canonical isomorphism
π_X⁻¹ F ≅ F, induced by the small-étale site isomorphism of geometric
Frobenius. -/
@[stacks 03SR] #check
  (AlgebraicGeometry.SchemeOverField.geometricFrobeniusSheafPullbackIso :
    ∀ {k : Type u} [Field k] [Fintype k] {p : ℕ} [Fact p.Prime]
      [CharP k p] [Algebra (ZMod p) k] (X : SchemeOverField k)
      (A : Type v) [Category.{w} A],
      (smallEtalePullback (geometricFrobenius_ofFiniteField X)).sheafPullback
          A X.left.smallEtaleTopology X.left.smallEtaleTopology ≅
        𝟭 (Sheaf X.left.smallEtaleTopology A))

/- Lemma 64.3.5 (2): for a sheaf F on X_étale there is a canonical isomorphism
F ≅ (π_X)_* F, induced by restriction along the inverse of the comparison
γ_U = (U.hom, F_U^f). -/
@[stacks 03SR] #check
  (AlgebraicGeometry.SchemeOverField.geometricFrobeniusSheafPushforwardIso :
    ∀ {k : Type u} [Field k] [Fintype k] {p : ℕ} [Fact p.Prime]
      [CharP k p] [Algebra (ZMod p) k] (X : SchemeOverField k)
      (A : Type v) [Category.{w} A],
      𝟭 (Sheaf X.left.smallEtaleTopology A) ≅
        (smallEtalePullback (geometricFrobenius_ofFiniteField X)).sheafPushforwardContinuous
          A X.left.smallEtaleTopology X.left.smallEtaleTopology)
