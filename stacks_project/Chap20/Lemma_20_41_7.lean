/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom.Complex
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite.Basic

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.41.7:
- primary domain: quasi-isomorphism invariance of internal-Hom complexes of `𝒪_X`-module
  cochain complexes on a ringed space;
- sampled owner declarations:
  `CategoryTheory.MonoidalClosed.Source.map`,
  `SheafOfModules.RingedSite.IHom.quasiIso_map`;
- best owner abstraction: the generic map and its reusable ringed-site quasi-isomorphism theorem
  in ReasLib;
- primitive data: the ambient ringed space together with the quasi-isomorphisms
  `(𝓛')^• ⟶ 𝓛^•` and `(𝓘')^• ⟶ 𝓘^•`;
- derived API: the ringed-space specialization of that owner theorem, with no parallel local
  wrapper for the internal-Hom comparison morphism or its quasi-isomorphism statement.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.7 for complexes of `𝒪_X`-modules on a ringed space;
- `core/canonical`: `CategoryTheory.MonoidalClosed.Source.map` and
  `SheafOfModules.RingedSite.IHom.quasiIso_map`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file therefore stays at the `bridge/view` layer and directly recalls the ReasLib owner,
without importing Chapter 21. -/

/- Lemma 20.41.7: for a ringed space `(X, 𝒪_X)`, if
`(𝓘')^• ⟶ 𝓘^•` is a quasi-isomorphism of K-injective complexes of `𝒪_X`-modules and
`(𝓛')^• ⟶ 𝓛^•` is a quasi-isomorphism of complexes of `𝒪_X`-modules, then the induced canonical
morphism `ℋom^•(𝓛^•, (𝓘')^•) ⟶ ℋom^•((𝓛')^•, 𝓘^•)`
is a quasi-isomorphism. In the project API this is the reusable ringed-site theorem specialized
to the canonical site of opens of `X`. -/
@[stacks 0A8S]
#check fun {L' L I' I : CochainComplex X.Modules ℤ}
    [I'.IsKInjective] [I.IsKInjective]
    (f : L' ⟶ L) (g : I' ⟶ I) (h_f : QuasiIso f) (h_g : QuasiIso g) ↦
  SheafOfModules.RingedSite.IHom.quasiIso_map f g h_f h_g

/- Companion check: the underlying induced morphism is the generic closed-monoidal map. -/
#check @CategoryTheory.MonoidalClosed.Source.map

/- Specialized ringed-site owner check for Lemma 20.41.7. -/
#check @SheafOfModules.RingedSite.IHom.quasiIso_map

end AlgebraicGeometry.RingedSpace
