/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Category.ModuleCat.Descent.BaseExtension
public import ReasLib.Algebra.Category.ModuleCat.Descent.Pushforward
public import ReasLib.LinearAlgebra.UniversallyInjective

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

namespace ModuleCat.DescentPushforward

universe u

/-- If an algebra map is universally injective, then scalar extension carries the
canonical descent-pushforward equalizer fork to a limiting fork. -/
theorem baseChangeIsLimit {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h_f : LinearMap.UniversallyInjective (Algebra.linearMap R S))
    (D : (ModuleCat.extendRestrictScalarsAdj.{u} (algebraMap R S)).toComonad.Coalgebra) :
    Nonempty (IsLimit (baseChangeFork (algebraMap R S) D)) := sorry

end ModuleCat.DescentPushforward

namespace RingHom

universe u

/-- For a homomorphism of commutative rings, descent for modules, effective descent for
modules, and universal injectivity of its underlying linear map are equivalent. -/
theorem tfae_descentForModules (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    List.TFAE [(algebraMap R S).DescentForModules,
      (algebraMap R S).EffectiveDescentForModules,
      LinearMap.UniversallyInjective (Algebra.linearMap R S)] := sorry

end RingHom
