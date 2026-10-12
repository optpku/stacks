/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 36.6.2 (1): if `X \ T` is retrocompact, the closed-support coreflector sends
`D_QCoh(𝒪_X)` to `D_QCoh,T(𝒪_X)`. -/
@[stacks 0G7G] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn.coreflector :
    ∀ (X : Scheme.{u}) (T : TopologicalSpace.Closeds X)
      (hT : IsRetrocompact ((T : Set X)ᶜ)),
      Scheme.DerivedQCoh X ⥤ Scheme.DerivedQCoh.SupportedOn X T)

/- Lemma 36.6.2 (2): the restricted closed-support coreflector is right adjoint to the
inclusion `D_QCoh,T(𝒪_X) ⥤ D_QCoh(𝒪_X)`. -/
@[stacks 0G7G] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn.adjunction :
    ∀ (X : Scheme.{u}) (T : TopologicalSpace.Closeds X)
      (hT : IsRetrocompact ((T : Set X)ᶜ)),
      Scheme.DerivedQCoh.SupportedOn.inclusion X T ⊣
        Scheme.DerivedQCoh.SupportedOn.coreflector X T hT)
