/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.Locality

/-!
# Compatibility import for locality of weakly étale scheme morphisms

The reusable locality API is owned by
`ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.Locality`.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- The weakly étale locality API remains available through this compatibility module. -/
#check
  (AlgebraicGeometry.Scheme.Hom.weaklyEtale_iff_locallyOfType :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      WeaklyEtale f ↔ LocallyOfType RingHom.WeaklyEtale f)
