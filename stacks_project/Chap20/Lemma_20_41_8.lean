/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom.Complex
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite.Basic
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.41.8:
- primary domain: K-injectivity of internal-Hom complexes for complexes of `𝒪_X`-modules on a
  ringed space;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.IsKInjective`,
  `(ihom L).obj I`,
  `SheafOfModules.RingedSite.IHom.isKInjective_of_isKFlat`;
- best owner abstraction: the canonical internal-Hom owner `(ihom L).obj I`, together with the
  ringed-site theorem `SheafOfModules.RingedSite.IHom.isKInjective_of_isKFlat`;
- primitive data: the ambient ringed space, the K-flat source complex, and the K-injective target
  complex;
- derived API: the K-injectivity statement for the canonical internal-Hom complex.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.8 for complexes of `𝒪_X`-modules on a ringed space;
- `core/canonical`: `(ihom L).obj I` and
  `SheafOfModules.RingedSite.IHom.isKInjective_of_isKFlat`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file should therefore stay at the `bridge/view` layer and directly recall the ringed-site
owner theorem instead of rebuilding a parallel ringed-space internal-Hom complex and its
differential term-by-term. -/

/- Lemma 20.41.8: if `𝓘^•` is a K-injective complex of `𝒪_X`-modules on a ringed space
`(X, 𝒪_X)` and `𝓛^•` is K-flat, then the canonical internal-Hom complex from `𝓛^•` to `𝓘^•`
is K-injective. In the project API this is exactly the ringed-site owner theorem specialized to
the canonical site of opens of `X`. -/
@[stacks 0A8T "K-injectivity of internal-Hom complexes"]
#check fun {L I : CochainComplex X.Modules ℤ}
    (hL : L.IsKFlat) [I.IsKInjective] ↦
  SheafOfModules.RingedSite.IHom.isKInjective_of_isKFlat
    (L := L) (I := I) hL

#check @SheafOfModules.RingedSite.IHom.isKInjective_of_isKFlat

end AlgebraicGeometry.RingedSpace
