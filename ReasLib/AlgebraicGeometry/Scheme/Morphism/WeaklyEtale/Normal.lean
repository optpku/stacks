/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.StrictHenselization
public import ReasLib.RingTheory.Henselian.Henselization.Normal

/-!
# Normal sources of weakly étale morphisms

This module records ascent of normality along weakly étale morphisms of schemes.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.WeaklyEtale

/-- The source of a weakly étale morphism with normal target is normal. -/
@[stacks 0950]
theorem isNormal {X Y : Scheme.{u}} (f : X ⟶ Y) [WeaklyEtale f]
    (hY : Y.isNormal) : X.isNormal := sorry

end AlgebraicGeometry.WeaklyEtale
