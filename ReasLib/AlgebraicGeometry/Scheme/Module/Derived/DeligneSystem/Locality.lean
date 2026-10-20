/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Triangulated
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open

/-!
# Locality of Deligne systems

This module relates Deligne-system presentations of a positive inverse system to those of
its restrictions to a finite open cover.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v

namespace AlgebraicGeometry.Scheme.ModuleDerived

set_option allowUnsafeReducibility true in
-- Local declaration justification (localized automation): unfolding the open-subscheme coercion exposes the canonical Noetherian restriction instance to typeclass search.
attribute [local reducible] Scheme.Opens.toScheme

variable {X U : Scheme.{v}} {j : U ⟶ X}
variable [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j]

/-- A positive inverse system of bounded coherent complexes is presented by a Deligne system
if and only if each of its restrictions to a member of a finite open cover is presented by a
Deligne system for the restricted open immersion. -/
theorem exists_proIso_deligne_iff_restrict
    (K : PNatInverseSystem Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    {r : ℕ} (W : Fin r → X.Opens) (hW : TopologicalSpace.IsOpenCover W) :
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
            S.proObject) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
