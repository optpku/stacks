/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.Locality
public import ReasLib.RingTheory.Etale.Weakly
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Differentials

/-!
# Formal unramifiedness of weakly étale scheme morphisms

Weakly étale morphisms of schemes are formally unramified, and consequently their sheaves of
relative differentials vanish.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.WeaklyEtale

/-- A weakly étale morphism of schemes is formally unramified. -/
instance (priority := 900) instFormallyUnramified {X Y : Scheme.{u}}
    (f : X ⟶ Y) [WeaklyEtale f] : FormallyUnramified f := sorry

/-- The sheaf of relative differentials of a weakly étale morphism is a zero object. -/
theorem isZero_relativeDifferentials {X Y : Scheme.{u}}
    (f : X ⟶ Y) [WeaklyEtale f] :
    CategoryTheory.Limits.IsZero (Ω[f.toShHom]) := sorry

end AlgebraicGeometry.WeaklyEtale
