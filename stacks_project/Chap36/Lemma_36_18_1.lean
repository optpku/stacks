/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Tensor
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.CochainComplex.Enriched
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.TensorWithObject

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedTensor

variable {X : Scheme.{u}}
variable (K : CochainComplex X.toRingedSpace.Modules ℤ)
/-- The homotopy-level tensor functor for a complex on a scheme, followed by the canonical
ringed-site derived localization. -/
abbrev sourceFunctor :=
  SheafOfModules.RingedSite.TensorWithObject.Derived.tensorSourceFunctor K

end AlgebraicGeometry.Scheme.DerivedTensor

/- Lemma 36.18.1 (09M3): derived tensoring with a complex whose homology sheaves are
quasicoherent has quasicoherent cohomology. -/
@[stacks 09M3] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.tensorFunctor_mem :
    ∀ {X : Scheme.{u}} (K : CochainComplex X.toRingedSpace.Modules ℤ)
      (hK : ∀ n : ℤ, RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
        (K.homology n))
      (M : DifferentialGradedModule.Derived.Category.{0, u} (endDGA.{u, u} K)),
      AlgebraicGeometry.Scheme.derivedQuasiCoherentModuleProperty X
        ((SheafOfModules.RingedSite.TensorWithObject.Derived.tensorFunctor K).obj M))
