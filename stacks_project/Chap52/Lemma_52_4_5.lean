/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Cohomology.Adic
public import stacks_project.Chap52.Lemma_52_4_4
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 52.4.5: if `I` has local-cohomological dimension one, then in every
integer degree the limit topology on the cohomology system of a coherent formal module
is the `I`-adic module topology. -/
@[stacks 0EH7] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.cohomologyLimitTopology_eq_adic :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.CoherentFormalModules
      ((Scheme.idealSheafDataOfIdealOnSpec I).comap f))
    (hcd : Ideal.LocalCohomology.dimension I I.fg_of_isNoetherianRing = 1)
    (p : ℤ),
    Functor.limitTopology (Scheme.CoherentFormalModules.cohomologySystem F f p) =
      Ideal.adicModuleTopology I
        (limit (Scheme.CoherentFormalModules.cohomologySystem F f p) : ModuleCat A))
