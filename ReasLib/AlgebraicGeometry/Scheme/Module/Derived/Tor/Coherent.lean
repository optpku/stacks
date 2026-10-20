/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor

@[expose] public section

/-!
# Coherence of Tor sheaves

Tor sheaves of coherent modules on a locally Noetherian scheme are coherent.
-/

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Every fixed-right Tor sheaf of two coherent modules on a locally Noetherian scheme is
coherent. -/
@[stacks 0AZS, instance]
theorem torRight_isCoherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F G : X.Modules) [F.IsCoherent] [G.IsCoherent] (p : ℕ) :
    (@RingedSpace.ModuleDerived.torRight X.toRingedSpace p F G
      (Scheme.Modules.hasDerivedTensorRight X)).IsCoherent := sorry

end AlgebraicGeometry.Scheme.Modules
