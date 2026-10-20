/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Amplitude
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)
variable (E : DifferentialGradedModule.Derived.Category.{u, v} A)
variable (hE : IsCompactObject E)

/-!
# Lemma 22.36.5 (09RA)

Every compact intrinsic derived object has a finite interval of homological degrees which detects
all outgoing morphisms.  The companion check displays the original DG-module-target formulation.
-/

@[stacks 09RA] #check
  (DifferentialGradedModule.Derived.hasFiniteHomologyWindow_of_isCompactObject A E hE :
    DifferentialGradedModule.Derived.hasFiniteHomologyWindow A E)
#check @DifferentialGradedModule.Derived.hasFiniteHomologyWindow
#check @DifferentialGradedModule.Derived.exists_module_homologyWindow_of_isCompactObject
#check @DifferentialGradedModule.Derived.detectedByHomologyOn
#check @DifferentialGradedModule.Derived.detectedByHomologyOn_iff
#check @DifferentialGradedModule.Derived.hom_eq_zero_of_detectedByHomologyOn
#check @DifferentialGradedModule.Derived.homologyVanishesOn_fromModules_iff
#check @DifferentialGradedModule.Derived.homologyIso
