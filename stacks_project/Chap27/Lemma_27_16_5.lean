/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Functor
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

universe u

#check
  (AlgebraicGeometry.RelativeProjFunctor :
    (S : AlgebraicGeometry.Scheme.{u}) →
      GradedAlgebraSheaf.{u, u} S.sheaf → Type (u + 1))

#check
  (AlgebraicGeometry.RelativeProjFunctor.toFunctor :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf)
      (F : AlgebraicGeometry.RelativeProjFunctor S 𝒜),
      AlgebraicGeometry.Schemeᵒᵖ ⥤ Type u)

/- Lemma 27.16.5: in Situation 27.15.1, the relative projective-spectrum
functor is representable by a scheme. -/
@[stacks 01NY] #check
  (AlgebraicGeometry.RelativeProjFunctor.instIsRepresentable :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf)
      [F : AlgebraicGeometry.RelativeProjFunctor S 𝒜],
      F.toFunctor.IsRepresentable)
