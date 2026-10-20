/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.FrobeniusColimit.ModuleStack
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Proposition 38.39.4 (1): finite locally free modules over the Frobenius-colimit
structure sheaves form an h-stack in groupoids. -/
@[stacks 0EXE] #check
  (AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit.moduleFiberedCategoryIsStack :
    ∀ (p : ℕ) [Fact p.Prime]
      (Schh : AlgebraicGeometry.ChosenBigHSite.{u, u}) (S : Schh.carrier)
      [AlgebraicGeometry.Scheme.IsCharP (Schh.toScheme.obj S) p],
      IsStack.InGroupoids (AlgebraicGeometry.ChosenBigHSite.bigTopology Schh S)
        (AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit.moduleFiberedCategory
          p Schh S).p)

/- Proposition 38.39.4 (2): over a quasi-compact and quasi-separated represented scheme,
the fibre of the Frobenius-colimit module stack is the core of the Frobenius colimit of
vector bundles. -/
@[stacks 0EXE]
#check
  (AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit.moduleFiberEquivVectorBundleColimit :
    ∀ (p : ℕ) [Fact p.Prime]
      (Schh : AlgebraicGeometry.ChosenBigHSite.{u, u}) (S : Schh.carrier)
      [AlgebraicGeometry.Scheme.IsCharP (Schh.toScheme.obj S) p] (U : Over S)
      [CompactSpace ((AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S).obj U)]
      [QuasiSeparatedSpace ((AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S).obj U)],
      -- Local instance justification (search instability): derive the represented scheme's characteristic only in the expected type.
      letI : AlgebraicGeometry.Scheme.IsCharP
          ((AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S).obj U) p :=
        AlgebraicGeometry.Scheme.Hom.isCharP_of_target (Schh.toScheme.map U.hom)
      Nonempty
        ((AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit.moduleFiberedCategory
            p Schh S).p.Fiber U ≌
          Core (AlgebraicGeometry.Scheme.FrobeniusColimit.vectorBundleColimit p
            ((AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S).obj U))))
