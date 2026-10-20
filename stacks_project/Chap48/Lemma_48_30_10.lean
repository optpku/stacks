/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Locality
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.ModuleDerived
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

universe v

set_option allowUnsafeReducibility true in
-- Local declaration justification (localized automation): unfolding the open-subscheme coercion exposes the canonical Noetherian restriction instance to typeclass search.
attribute [local reducible] Scheme.Opens.toScheme

/- Lemma 48.30.10: let `j : U ⟶ X` be an open immersion of Noetherian schemes and
`K` a positive inverse system in `Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]`. For a
finite open cover `W` of `X`, the pro-object presented by `K` is isomorphic to that of a
Deligne system for `j` if and only if this holds after restriction to every `W i`, with
respect to the restricted open immersion `j ∣_ W i`. -/
@[stacks 0G4T] #check
  (@AlgebraicGeometry.Scheme.ModuleDerived.exists_proIso_deligne_iff_restrict :
    ∀ {X U : Scheme.{v}} {j : U ⟶ X} [IsNoetherian X] [IsNoetherian U]
      [IsOpenImmersion j]
      (K : PNatInverseSystem Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
      {r : ℕ} (W : Fin r → X.Opens) (hW : TopologicalSpace.IsOpenCover W),
      (∃ S : DeligneSystem j,
        Nonempty (boundedProObject K ≅ S.proObject)) ↔
        ∀ i : Fin r,
          ∃ S : DeligneSystem
            (j ∣_ W i : U.restrict (j ⁻¹ᵁ W i).isOpenEmbedding ⟶
              X.restrict (W i).isOpenEmbedding),
          Nonempty
            ((@Pro.lim (DerivedCategory (X.restrict (W i).isOpenEmbedding).Modules) _
                (OrderDual ℕ+) _ _ _ _).obj
                  (K ⋙ ambient (SheafOfModules.isCoherent X.ringCatSheaf) ⋙
                    RingedSpace.modulePullbackDerived (W i).ι.toShHom) ≅
              S.proObject))
