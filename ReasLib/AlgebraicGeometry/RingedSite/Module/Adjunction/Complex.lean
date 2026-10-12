/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Complex
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Complex
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback-pushforward adjunction on complexes

The module pullback-pushforward adjunction lifts degreewise to unbounded cochain complexes.  This
file is the shared owner for the lifted adjunction and its Hom equivalence.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

namespace RingedSite.Hom

/-- The degreewise pullback of complexes is left adjoint to degreewise pushforward. -/
@[stacks 0FRE "complex pullback-pushforward adjunction"]
noncomputable def modulePullbackPushforwardComplexAdjunction.{z, uX, vX, uY, vY, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint] :
    f.modulePullbackComplex.{z} ⊣ f.modulePushforwardComplex.{z} :=
  Adjunction.mapHomologicalComplexAdjunction
    (modulePullbackPushforwardAdjunction.{z} f) (up ℤ)

/-- The Hom equivalence induced by pullback-pushforward adjunction on unbounded cochain
complexes. -/
noncomputable def modulePullbackComplexHomEquiv.{z, uX, vX, uY, vY, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint]
    (K : CochainComplex (ModuleCat.{z} Y) ℤ)
    (L : CochainComplex (ModuleCat.{z} X) ℤ) :
    (f.modulePullbackComplex.{z}.obj K ⟶ L) ≃
      (K ⟶ f.modulePushforwardComplex.{z}.obj L) :=
  (modulePullbackPushforwardComplexAdjunction.{z} f).homEquiv K L

end RingedSite.Hom
