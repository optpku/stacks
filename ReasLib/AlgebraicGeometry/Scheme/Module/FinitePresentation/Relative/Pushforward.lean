/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.Algebra.Module.FinitePresentation.Relative.FiniteExtension
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For a finite morphism over a locally finite type base, a quasicoherent scheme module is
relatively finitely presented if and only if its pushforward is relatively finitely presented. -/
@[stacks 09T9]
theorem isFinitePresentationOver_iff_pushforward_of_isFinite
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsFinite f]
    [LocallyOfFiniteType g] (F : X.Modules) [F.IsQuasicoherent] :
    F.IsFinitePresentationOver (f ≫ g) ↔
      ((Scheme.Modules.pushforward f).obj F).IsFinitePresentationOver g := sorry

end AlgebraicGeometry.Scheme.Modules
