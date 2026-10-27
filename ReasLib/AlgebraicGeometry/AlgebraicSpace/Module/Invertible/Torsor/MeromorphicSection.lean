/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Invertible.Torsor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.RegularPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction.Pullback.Criteria

/-! # Meromorphic sections on multiplicative torsors

The tautological trivialization of an invertible module on its multiplicative
torsor identifies a pulled-back meromorphic section with a meromorphic function.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Pull back a meromorphic section to the multiplicative torsor and transport
it through the tautological trivialization to the structure module. -/
noncomputable def gmTorsorTrivMeromorphicSection {X : AlgebraicSpace S}
    (L : X.Modules) [isInvertibleObject L] (s : meromorphicSections X L) :
    meromorphicSections (Modules.gmTorsor L) (𝟙_ (Modules.gmTorsor L).Modules) :=
  sectionsMap (meromorphicSectionSheafMap (Modules.gmTorsorTriv L).hom)
    (MeromorphicConstruction.Pullback.pullback (Modules.gmTorsorπ L) L s)

/-- The meromorphic function induced on the multiplicative torsor is the
canonical pullback section transported by the tautological trivialization. -/
theorem gmTorsorTrivMeromorphicSection_def {X : AlgebraicSpace S}
    (L : X.Modules) [isInvertibleObject L] (s : meromorphicSections X L) :
    gmTorsorTrivMeromorphicSection L s =
      sectionsMap (meromorphicSectionSheafMap (Modules.gmTorsorTriv L).hom)
        (MeromorphicConstruction.Pullback.pullback (Modules.gmTorsorπ L) L s) :=
  rfl

/-- Pullback to the multiplicative torsor followed by its tautological
trivialization preserves regularity of a meromorphic section. -/
theorem isRegularMeromorphicSection_gmTorsorTriv {X : AlgebraicSpace S}
    (L : X.Modules) [isInvertibleObject L] (s : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s) :
    IsRegularMeromorphicSection (Modules.gmTorsor L) (𝟙_ (Modules.gmTorsor L).Modules)
      (gmTorsorTrivMeromorphicSection L s) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
