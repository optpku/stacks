/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Support
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.ExtensionByZero.Comparison

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.33.6:
- primary domain: support conditions on cohomology sheaves of derived `𝒪_X`-modules and
  their interaction with restriction, open pushforward, and extension by zero;
- sampled owner declarations:
  `DerivedCategory (RingedSpace.Modules X)`,
  `SheafOfModules.support`,
  `moduleSupport`,
  `moduleSupportedOn`,
  `ModuleDerived.IsSupportedOn`,
  `moduleExtensionByZeroFromOpenDerived`,
  `modulePushforwardFromOpenDerived`;
- best owner abstraction: ReasLib owns the support notion via
  `SheafOfModules.support`, `moduleSupport`, and the support-on-a-subset owner
  `moduleSupportedOn`, while Chapter 13 already owns the degreewise cohomology predicate
  `ModuleDerived.IsSupportedOn`; the ambient derived category `D(𝒪_X)`, the
  owner-file derived lower shriek `moduleExtensionByZeroFromOpenDerived X U`, the derived
  restriction owner `moduleRestrictionToOpenDerived X U`, and the derived open pushforward
  `modulePushforwardFromOpenDerived U` are reused from earlier Chapter 20 files, so this file
  should state the comparison directly through those existing owners rather than introducing local
  wrapper notions for support or open-subspace derived categories;
- primitive data: for part `(1)`, an open subset `U` and a derived module on `X` whose
  cohomology is supported on `U`; for part `(2)`, an open subset `U`, a closed subset `T ⊆ X`
  contained in `U`, and a derived module on that open subspace whose cohomology is supported on
  the induced subset `Subtype.val ⁻¹' T`;
- derived API: the two comparison isomorphism statements.

Source/core/bridge triage:
- `source-facing`: the two comparison statements in Lemma 20.33.6;
- `core/canonical`: `DerivedCategory (RingedSpace.Modules X)`, `SheafOfModules.support`,
  `ModuleDerived.IsSupportedOn`, `moduleSupportedOn`,
  `moduleExtensionByZeroFromOpenDerived`,
  `moduleRestrictionToOpenDerived`, `modulePushforwardFromOpenDerived`;
- `bridge/view`: the textbook term `Rj_*(E|_U)` is presented by the canonical composite owner
  `moduleRestrictionToOpenDerived X U ⋙ modulePushforwardFromOpenDerived U`.
-/

section

variable {X : RingedSpace.{u}}

-- Local declaration justification (source-local notation): these abbreviations keep the two
-- open-subspace comparison statements close to their standard mathematical notation.
local notation "DModX" => ModuleDerived X
local notation "DMod[" U "]" => moduleDerivedOnOpen X U
local notation "DRes[" U "]" => moduleRestrictionToOpenDerived X U
local notation "DExt[" U "]" => moduleExtensionByZeroFromOpenDerived X U
local notation "DPush[" U "]" => modulePushforwardFromOpenDerived U
local notation "RPush[" U "]" => DRes[U] ⋙ DPush[U]

-- Proof sketch: let `V = X \ U`. If every cohomology sheaf of `E` is supported on `U`, then
-- each cohomology sheaf restricts to zero on `V`, hence `E|_V = 0`. The restriction of
-- `Rj_* (E|_U)` to `V` is also zero, while its restriction to `U` identifies with `E|_U`.
-- Comparing on the open cover `X = U ∪ V` gives the claimed isomorphism.
/-- Lemma 20.33.6 (1), comparison-map form: if `j : U ↪ X` is an open subspace and every
cohomology sheaf of `E ∈ D(𝒪_X)` is supported on `U`, then the canonical map
`E ⟶ Rj_*(E|_U)` is an isomorphism. -/
@[stacks 08DF]
theorem isIso_restrictionToOpenDerivedToPushforwardFromOpenDerived_of_cohomologySupported
    (U : Opens X.carrier) (E : DModX)
    (hE : ModuleDerived.IsSupportedOn E U) :
    IsIso ((OpenSubspace.Pushforward.derivedAdjunction X U).unit.app E) := sorry

/-- Lemma 20.33.6 (1): if `j : U ↪ X` is an open subspace and every cohomology sheaf of
`E ∈ D(𝒪_X)` is supported on `U`, then `E` is canonically isomorphic to `Rj_*(E|_U)`. Here
`Rj_*(E|_U)` is formalized by `(RPush[U]).obj E`. -/
@[stacks 08DF]
theorem isIsomorphic_restrictionToOpenDerived_pushforwardFromOpenDerived_of_cohomologySupported
    (U : Opens X.carrier)
    (E : DModX)
    (hE : ModuleDerived.IsSupportedOn E U) :
    IsIsomorphic E ((RPush[U]).obj E) := sorry

-- Proof sketch: the Chapter 20 lower shriek `j_!` is the derived extension-by-zero owner
-- `moduleExtensionByZeroFromOpenDerived X U`. For a closed subset `T ⊆ X` contained in `U`, set
-- `V = X \ T` and `W = U ∩ V`. The support hypothesis on `Subtype.val ⁻¹' T` implies that `F`
-- restricts to zero on `W`, so both `j_! F` and `Rj_* F` vanish on `V`; their restrictions to
-- `U` both identify with `F`. Comparing on the open cover `X = U ∪ V` gives the canonical
-- comparison `j_! F ⟶ Rj_* F` as an isomorphism.
/-- Lemma 20.33.6 (2), comparison-map form: if `j : U ↪ X` is an open subspace and every
cohomology sheaf of `F ∈ D(𝒪_U)` is supported on the induced subset `Subtype.val ⁻¹' T ⊆ U`
of a closed subset `T ⊆ X` contained in `U`, then the canonical map `j_! F ⟶ Rj_* F` is an
isomorphism. -/
@[stacks 08DF]
theorem isIso_extensionByZeroDerivedToPushforwardFromOpen_of_cohomologySupported
    (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    {T : Set X}
    (hT_closed : IsClosed T) (hTU : T ⊆ U)
    (F : DMod[U])
    (hF : ModuleDerived.IsSupportedOn F (Subtype.val ⁻¹' T)) :
    IsIso ((OpenSubspace.ExtensionByZero.derivedToPushforward X U).app F) := sorry

/-- Lemma 20.33.6 (2): if `j : U ↪ X` is an open subspace and every cohomology sheaf of
`F ∈ D(𝒪_U)` is supported on the induced subset `Subtype.val ⁻¹' T ⊆ U` of a closed
subset `T ⊆ X` contained in `U`, then `j_! F` is canonically isomorphic to `Rj_* F`. Here
`j_!` is formalized by `(DExt[U]).obj F` and `Rj_*` by `(DPush[U]).obj F`; the support condition
on the open subspace is expressed canonically by `Subtype.val ⁻¹' T`. -/
@[stacks 08DF]
theorem isIsomorphic_extensionByZeroDerived_pushforwardFromOpen_of_cohomologySupported
    (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    {T : Set X}
    (hT_closed : IsClosed T) (hTU : T ⊆ U)
    (F : DMod[U])
    (hF : ModuleDerived.IsSupportedOn F (Subtype.val ⁻¹' T))
    : IsIsomorphic ((DExt[U]).obj F) ((DPush[U]).obj F) := sorry

end

end AlgebraicGeometry.RingedSpace
