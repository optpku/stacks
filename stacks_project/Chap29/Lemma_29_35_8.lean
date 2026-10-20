/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.ClosedImmersion
import StacksCheckRecall

/-!
# Lemma 29.35.8

Closed immersions are unramified, with G-unramifiedness detected by finite type of the kernel ideal
sheaf.

@stack 02GC
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/- Lemma 29.35.8 (1): a closed immersion is unramified. -/
@[stacks 02GC] #check (AlgebraicGeometry.IsClosedImmersion.unramified :
  ∀ {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i], Unramified i)

/- Lemma 29.35.8 (2): a closed immersion is G-unramified exactly when its kernel ideal sheaf is
of finite type. -/
@[stacks 02GC] #check
  (AlgebraicGeometry.IsClosedImmersion.gUnramified_iff_idealSheaf_isFiniteType :
    ∀ {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i],
      GUnramified i ↔
        SheafOfModules.IsFiniteType (RingedSpace.Hom.idealSheaf i.toShHom))

end AlgebraicGeometry
