/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem.PseudoCoherent
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

universe u

/- Lemma 77.12.4: in Situation 77.12.1, let K be as in Lemma 77.12.2,
equivalently ((DerivedQCoh.inclusion X).rightAdjoint.obj Klim).obj for an
ambient homotopy limit Klim of a tower identified with the pushed stage
sheaves ℱ n, including successor maps, in D(𝒪_X). Then K is
pseudo-coherent relative to A, i.e.
ModuleDerived.IsPseudoCoherentOver (toBase X) K. -/
@[stacks 0CX7] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem.coheratorHomotopyLimit_isPseudoCoherentOver :
    ∀ (S : ProperFlatFormalSystem.{u})
      [∀ sq : EtaleSquare (toBase S.space),
        (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
          (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
      [IsQuasiCompact S.space] [IsAbsolutelyQuasiSeparated S.space]
      (F : SequentialInverseSystem (QCoh S.space))
      (stageIso : ∀ n, (QCoh.inclusion S.space).obj (F.obj (Opposite.op n)) ≅
        S.pushforwardModule n),
      (∀ n, (QCoh.inclusion S.space).map (F.stepMap n) ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ S.pushforwardStep n) →
      ∀ (Klim : ModuleDerived S.space),
      HomotopyLimit.IsOf
        (F ⋙ QCoh.inclusion S.space ⋙
          DerivedCategory.singleFunctor S.space.Modules (0 : ℤ)) Klim →
      @ModuleDerived.IsPseudoCoherentOver _ _ _ (toBase S.space)
        (@locallyOfFiniteType_of_locallyOfFinitePresentation _ _ _ (toBase S.space)
          S.toBase_finitePresentation.toLocallyOfFinitePresentation)
        ((DerivedQCoh.inclusion S.space).rightAdjoint.obj Klim).obj)
