/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Pushforward.AlongDerived

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpace.Hom RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

open OpenSubspace.Pushforward

/- Domain-style sampling for Lemma 20.33.2:
- primary domain: Mayer-Vietoris distinguished triangles in `D(𝒪_X)` written with
  derived restriction to open subspaces and derived direct image along the open inclusions;
- sampled owner declarations:
  `OpenSubspace.Pushforward.derivedUnit`,
  `OpenSubspace.Pushforward.derivedRestriction`,
  `modulePushforwardFromOpenDerived`,
  `Triangle.mk`;
- best owner abstraction:
  `source-facing`: the Mayer-Vietoris distinguished triangle
    `R(𝟙_X)_* E ⟶ Rj_{U,*}(E|_U) ⊞ Rj_{V,*}(E|_V) ⟶
      Rj_{U ∩ V,*}(E|_{U ∩ V}) ⟶ R(𝟙_X)_* E⟦(1 : ℤ)⟧`,
    together with the objectwise identification `R(𝟙_X)_* E ≅ E`;
  `core/canonical`: the ReasLib open-subspace owner layer
    `OpenSubspace.Pushforward.derivedUnit (𝟙 X) U`,
    `OpenSubspace.Pushforward.derivedRestriction (𝟙 X) h`,
    `modulePushforwardFromOpenDerived U`, and `Triangle.mk`;
  `bridge/view`: the theorem-level identity-pushforward comparisons
    `ringedSpaceModuleDerivedPushforward_id_isomorphic` and
    `ringedSpaceModuleDerivedPushforward_obj_id_isomorphic`.
- primitive data: the opens `U, V`, the cover equation `U ⊔ V = ⊤`, and the derived object `E`;
- derived API: the canonical unit and overlap-restriction natural transformations, together with
  the source-facing distinguished triangle statement below.

Source/core/bridge triage:
- `source-facing`: `ringedSpaceModule_derivedMayerVietoris_triangle`;
- `core/canonical`: `OpenSubspace.Pushforward.derivedUnit`,
  `OpenSubspace.Pushforward.derivedRestriction`,
  `modulePushforwardFromOpenDerived`, and `Triangle.mk`;
- `bridge/view`: `ringedSpaceModuleDerivedPushforward_id_isomorphic` and
  `ringedSpaceModuleDerivedPushforward_obj_id_isomorphic`.

This file therefore stays at the source-facing layer: it states the direct-image
Mayer-Vietoris triangle itself, while reusing the ReasLib open restriction and open
pushforward functors on the theorem surface. -/

section

variable {X : RingedSpace.{u}}

-- Proof sketch: choose a K-injective complex representing `E`, identify the three displayed
-- terms with the pushforwards of its restrictions to `U`, `V`, and `U ∩ V`, use the classical
-- Mayer-Vietoris short exact sequence of complexes for the cover `U ∪ V = X`, and then apply
-- the distinguished triangle attached to a short exact sequence of complexes in the derived
-- category. The companion bridge theorem below identifies `R(𝟙_X)_* E` with the textbook vertex
-- `E`.

/-- The identity-specialized derived pushforward functor is canonically isomorphic to the identity
on `D(𝒪_X)`. -/
theorem ringedSpaceModuleDerivedPushforward_id_isomorphic :
    IsIsomorphic (R(𝟙 X)_*) (𝟭 (ModuleDerived X)) := sorry

/-- Objectwise companion to `ringedSpaceModuleDerivedPushforward_id_isomorphic`. -/
theorem ringedSpaceModuleDerivedPushforward_obj_id_isomorphic (E : ModuleDerived X) :
    IsIsomorphic ((R(𝟙 X)_*).obj E) E := sorry

/- Lemma 20.33.2: if a ringed space `X` is covered by two opens `U` and `V`, then the canonical
identity-pushforward Mayer-Vietoris triangle
`R(𝟙_X)_* E ⟶ Rj_{U,*}(E|_U) ⊞ Rj_{V,*}(E|_V) ⟶
Rj_{U ∩ V,*}(E|_{U ∩ V}) ⟶ R(𝟙_X)_* E⟦(1 : ℤ)⟧`
is distinguished for every `E ∈ D(𝒪_X)`. The companion theorem
`ringedSpaceModuleDerivedPushforward_obj_id_isomorphic` recovers the textbook presentation with
`E` in the left and right vertices. -/
@[stacks 08BV]
theorem ringedSpaceModule_derivedMayerVietoris_triangle
    (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    ∃ δ : alongDerived (𝟙 X) (U ⊓ V) ⟶
        R(𝟙 X)_* ⋙ shiftFunctor (ModuleDerived X) (1 : ℤ),
      ∀ E : ModuleDerived X,
        Triangle.mk
            ((biprod.lift
              (derivedUnit (𝟙 X) U)
              (derivedUnit (𝟙 X) V)).app E)
            ((biprod.desc
              (derivedRestriction (𝟙 X) (inf_le_left : U ⊓ V ≤ U))
              (-(derivedRestriction (𝟙 X) (inf_le_right : U ⊓ V ≤ V)))).app E)
            (δ.app E) ∈ distTriang (ModuleDerived X) := sorry

/-- Objectwise companion to `ringedSpaceModule_derivedMayerVietoris_triangle`. -/
theorem ringedSpaceModuleDerivedMayerVietorisTriangle
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (E : ModuleDerived X) :
    ∃ δ : (alongDerived (𝟙 X) (U ⊓ V)).obj E ⟶
        ((R(𝟙 X)_*).obj E)⟦(1 : ℤ)⟧,
      Triangle.mk
          ((biprod.lift
            (derivedUnit (𝟙 X) U)
            (derivedUnit (𝟙 X) V)).app E)
          ((biprod.desc
            (derivedRestriction (𝟙 X) (inf_le_left : U ⊓ V ≤ U))
            (-(derivedRestriction (𝟙 X) (inf_le_right : U ⊓ V ≤ V)))).app E)
          δ ∈ distTriang (ModuleDerived X) := sorry

end

end AlgebraicGeometry.RingedSpace
