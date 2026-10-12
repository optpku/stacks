/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.RelativeDualizing

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 48.15.1 -/
@[stacks 0A9W] #check
  (AlgebraicGeometry.Scheme.ProjectiveBundle.rightAdjointStructureSheaf_isomorphic :
    ∀ {Y P : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
      (π : P ⟶ Y) (ℰ : Y.Modules)
      (hπ : AlgebraicGeometry.Scheme.ProjectiveBundle.Representation π ℰ) (n : ℕ)
      [SheafOfModules.IsFiniteLocallyFreeOfRank (n + 1) ℰ]
      (a : AlgebraicGeometry.Scheme.DerivedQCoh Y ⥤
        AlgebraicGeometry.Scheme.DerivedQCoh P)
      (aAdjunction :
        AlgebraicGeometry.Scheme.ProjectiveBundle.derivedPushforward π ℰ hπ n ⊣ a),
      IsIsomorphic
        (AlgebraicGeometry.Scheme.ProjectiveBundle.relativeDualizingObject π ℰ hπ n)
        (a.obj (AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf Y)))

/- Lemma 48.15.1 (2) -/
@[stacks 0A9W]
#check
  (AlgebraicGeometry.ProjectiveSpaceOver.rightAdjointStructureSheaf_isomorphic_twist :
    ∀ {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y] (n : ℕ)
      (P : AlgebraicGeometry.ProjectiveSpaceOver Y n)
      (a : AlgebraicGeometry.Scheme.DerivedQCoh Y ⥤
        AlgebraicGeometry.Scheme.DerivedQCoh P.scheme)
      (aAdjunction : AlgebraicGeometry.ProjectiveSpaceOver.derivedPushforward P ⊣ a),
      IsIsomorphic (AlgebraicGeometry.ProjectiveSpaceOver.relativeDualizingObject P)
        (a.obj (AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf Y)))
