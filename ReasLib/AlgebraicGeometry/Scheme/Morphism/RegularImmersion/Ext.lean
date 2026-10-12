/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion

/-!
# Ext vanishing for regular closed immersions

Ext from the pushforward along a regular closed immersion to a locally free module sheaf
vanishes below the rank of the conormal sheaf.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsRegularClosedImmersion

/-- For a regular closed immersion with conormal sheaf of rank `c`, Ext from the pushforward
of any module sheaf to a locally free module sheaf vanishes in degrees below `c`. -/
theorem extPushforwardSubsingleton
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsRegularClosedImmersion i]
    (c : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (F : Z.Modules) (E : X.Modules) [E.IsLocallyFree] (q : ℕ) (hq : q < c) :
    Subsingleton (@CategoryTheory.Abelian.Ext X.Modules inferInstance inferInstance
      (@CategoryTheory.IsGrothendieckAbelian.hasExt X.Modules inferInstance inferInstance
        (SheafOfModules.isGrothendieckAbelian X.ringCatSheaf))
      ((Scheme.Modules.pushforward i).obj F) E q) := sorry

end AlgebraicGeometry.IsRegularClosedImmersion
