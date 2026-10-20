/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CoveringGluing
import StacksCheckRecall

/-!
# Lemma 85.24.5

Derived modules on a covering, with cocycle isomorphisms, vanishing negative
self-Ext sheaves, and a uniform lower cohomological bound, glue uniquely up to
a unique compatible isomorphism.
-/

open CategoryTheory CategoryTheory.Limits
open RingedSite.ModuleDerived

universe ι u v w

/- Lemma 85.24.5: existence of a global derived module with compatible local
identifications. -/
@[stacks 0GMG] #check (RingedSite.ModuleDerived.CoveringFamily.exists_solution :
  ∀ {C : RingedSite.{u, v, w}} {X : C}
    [HasPullbacks C.carrier] [UnivLE.{max u v, w}]
    {𝒰 : FormalCoproduct.{ι} (Over X)} (G : CoveringFamily C X 𝒰),
    𝒰.toSieve ∈ C.siteTopology X →
    G.negativeSheafSelfExt → G.uniformlyBoundedBelow →
    Nonempty (CoveringFamily.Solution G))

#check (RingedSite.ModuleDerived.CoveringFamily.unique_hom_solution :
  ∀ {C : RingedSite.{u, v, w}} {X : C}
    [HasPullbacks C.carrier] [UnivLE.{max u v, w}]
    {𝒰 : FormalCoproduct.{ι} (Over X)} (G : CoveringFamily C X 𝒰),
    𝒰.toSieve ∈ C.siteTopology X →
    G.negativeSheafSelfExt → G.uniformlyBoundedBelow →
    ∀ (S S' : CoveringFamily.Solution G),
      ∃ e : S.obj ≅ S'.obj,
        CoveringFamily.Solution.IsCompatibleIso S S' e ∧
          ∀ e' : S.obj ≅ S'.obj, CoveringFamily.Solution.IsCompatibleIso S S' e' →
            e'.hom = e.hom)
