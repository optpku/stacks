/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.RelativeDualizing
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 86.8.3 (1): the right adjoint's value on the structure sheaf is relatively perfect. -/
@[stacks 0E5V] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RelativeDualizing.isPerfectRelativeTo :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [IsAffine Y] → [Proper f] → [Flat f] → [FinitePresentation f] →
      ∀ (a : DerivedQCoh Y ⥤ DerivedQCoh X)
        (aAdjunction : DerivedQCoh.pushforwardCohomologyIn f ⊣ a),
        ModuleDerived.IsPerfectRelativeTo f (a.obj (DerivedQCoh.structureSheaf Y)).obj)

/- Lemma 86.8.3 (2): its derived pushforward has no positive cohomology sheaves. -/
@[stacks 0E5V] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RelativeDualizing.pushforward_cohomology_isZero_of_pos :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [IsAffine Y] → [Proper f] → [Flat f] → [FinitePresentation f] →
      ∀ (a : DerivedQCoh Y ⥤ DerivedQCoh X)
        (aAdjunction : DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
        (i : ℤ) (hi : 0 < i),
        IsZero (ModuleDerived.cohomologySheaf
          ((DerivedQCoh.pushforwardCohomologyIn f).obj
            (a.obj (DerivedQCoh.structureSheaf Y))).obj i))

/- Lemma 86.8.3 (3): its canonical scalar homothety is an isomorphism. -/
@[stacks 0E5V] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RelativeDualizing.homothety_isIso :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [IsAffine Y] → [Proper f] → [Flat f] → [FinitePresentation f] →
      ∀ (a : DerivedQCoh Y ⥤ DerivedQCoh X)
        (aAdjunction : DerivedQCoh.pushforwardCohomologyIn f ⊣ a),
        IsIso (ModuleDerived.InternalHom.homothety
          (a.obj (DerivedQCoh.structureSheaf Y)).obj))
