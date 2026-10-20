/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.BaseChange.InternalHom
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Functoriality.Perfect

@[expose] public section

noncomputable section

open CategoryTheory
open DerivedCategory

universe u

namespace CategoryTheory.ModuleCat

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

/-- If a coefficient algebra is perfect and Tor independent of the base-change algebra, then
the trivial-duality base-change morphism is an isomorphism for every derived module. -/
theorem trivialDualityBaseChangeMap_isIso_of_isPerfect
    (K : DerivedCategory (ModuleCat.{u} R))
    (hA : (ModuleCat.of R A).IsPerfect)
    (hTor : Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R')) :
    IsIso (trivialDualityBaseChangeMap K hTor) := sorry

end CategoryTheory.ModuleCat
