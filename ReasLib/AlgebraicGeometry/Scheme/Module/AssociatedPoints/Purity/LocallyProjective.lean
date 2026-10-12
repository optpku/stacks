/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.FiniteType

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite-type quasicoherent module whose pushforward along a finite-type affine morphism
is locally projective is universally pure over the target. -/
theorem isUniversallyPureOver_of_pushforward_isLocallyProjective
    {X S : Scheme.{u}} (f : X ⟶ S) [f.FiniteType] [IsAffineHom f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    [((Scheme.Modules.pushforward f).obj F).IsLocallyProjective] :
    F.IsUniversallyPureOver f := sorry

/-- For an affine finitely presented morphism and a finitely presented module flat over the
base, local projectivity of the pushforward is equivalent to relative purity. -/
theorem pushforward_isLocallyProjective_iff_isPureOver
    {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f] [IsAffineHom f]
    (F : X.Modules) [F.IsFinitePresentation] (h_flat : flatOver F f) :
    ((Scheme.Modules.pushforward f).obj F).IsLocallyProjective ↔ F.IsPureOver f := sorry

end AlgebraicGeometry.Scheme.Modules
