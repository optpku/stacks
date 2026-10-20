/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Colimit.Pullback

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.FrobeniusColimit

#check (vectorBundlesPullback : ∀ {S T : Scheme.{u}} (f : T ⟶ S),
  vectorBundles S ⥤ vectorBundles T)

#check (IsStagewisePullback : ∀ (p : ℕ) [Fact p.Prime] {S T : Scheme.{u}}
  [S.IsCharP p] [T.IsCharP p] (f : T ⟶ S)
  (G : vectorBundleColimit p S ⥤ vectorBundleColimit p T), Prop)

end AlgebraicGeometry.Scheme.FrobeniusColimit
