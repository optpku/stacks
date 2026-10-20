/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap36.«36_6_4_1»
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.Acyclicity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 36.6.5: the extended ordered Čech complex associated to global sections `f`
and a module sheaf `ℱ` is acyclic after restriction to `⨆ i, X.basicOpen (f i)`, whose
carrier is `(X.zeroLocus (Set.range f))ᶜ`. -/
@[stacks 0G7K] #check
  (ModuleCech.ofSections_restrict_acyclic :
    ∀ {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules),
      (((Scheme.Modules.restrictFunctor (⨆ i, X.basicOpen (f i)).ι).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (ModuleCech.ofSections f ℱ)).Acyclic)

end
