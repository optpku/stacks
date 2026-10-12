/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative
import ReasLib.Algebra.Module.FinitePresentation.Relative.BaseChange

/-!
# Base change of relative finite presentation for scheme modules

Relative finite presentation of quasi-coherent scheme modules is preserved by pullback along
an arbitrary morphism of base schemes.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Pulling a quasi-coherent scheme module across a cartesian base change preserves finite
presentation relative to the base. -/
theorem isFinitePresentationOver_pullback_fst
    {S X S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] (hF : F.IsFinitePresentationOver f) :
    ((Scheme.Modules.pullback (pullback.fst f g)).obj F).IsFinitePresentationOver
      (pullback.snd f g) := sorry

namespace IsFinitePresentationOver

/-- Pullback along a locally finitely presented morphism preserves relative finite
presentation of a quasi-coherent scheme module. -/
theorem pullback {X Y S : Scheme.{u}} {g : Y ⟶ S} [LocallyOfFiniteType g]
    {G : Y.Modules} [G.IsQuasicoherent] (hG : G.IsFinitePresentationOver g)
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    ((Scheme.Modules.pullback f).obj G).IsFinitePresentationOver (f ≫ g) := sorry

end IsFinitePresentationOver

end AlgebraicGeometry.Scheme.Modules
