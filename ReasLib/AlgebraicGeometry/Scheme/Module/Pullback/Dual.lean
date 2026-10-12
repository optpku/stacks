/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive
public import ReasLib.CategoryTheory.Monoidal.Closed.LaxMonoidal.Dualizable
import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree.Dualizable

/-!
# Pullback of dual scheme modules

This file constructs the canonical comparison from the pullback of a module dual to the dual
of its pullback and records its invertibility for finite locally free modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical comparison from the pullback of a module dual to the dual of its pullback. -/
noncomputable def pullbackDualComparison {Z Z' : Scheme.{u}} (g : Z' ⟶ Z)
    (N : Z.Modules) :
    (pullback g).obj (dual N) ⟶ dual ((pullback g).obj N) :=
  @Functor.LaxMonoidal.InternalHom.comparison _ _ _ _ _ _
      (pullback g) (pullbackMonoidal g).toLaxMonoidal N (𝟙_ Z.Modules) _ _ ≫
    (ihom ((pullback g).obj N)).map (pullbackUnitIso g).hom

/-- The dual-pullback comparison is invertible for a finite locally free module. -/
noncomputable instance pullbackDualComparison_isIso {Z Z' : Scheme.{u}} (g : Z' ⟶ Z)
    (N : Z.Modules) [IsFiniteLocallyFree N] :
    IsIso (pullbackDualComparison g N) := sorry

/-- The canonical isomorphism between the pullback of a finite locally free module's dual and
the dual of its pullback. -/
noncomputable def pullbackDualIso {Z Z' : Scheme.{u}} (g : Z' ⟶ Z)
    (N : Z.Modules) (hN : IsFiniteLocallyFree N) :
    (pullback g).obj (dual N) ≅ dual ((pullback g).obj N) :=
  @asIso _ _ _ _ (pullbackDualComparison g N)
    (@pullbackDualComparison_isIso _ _ g N hN)

end AlgebraicGeometry.Scheme.Modules
