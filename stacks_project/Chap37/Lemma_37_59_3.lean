/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap37.Definition_37_59_2
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Cohomology
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.59.3 (1): for a locally finite type morphism, relative `m`-pseudo-coherence
implies that the cohomology sheaf in every degree above `m` is quasi-coherent. -/
@[stacks 0CSU] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver.higherCohomology_isQuasicoherent :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
      {E : RingedSpace.ModuleDerived X.toRingedSpace} {m i : ℤ},
      Scheme.ModuleDerived.IsMPseudoCoherentOver f E m → m < i →
        (RingedSpace.ModuleDerived.cohomologySheaf E i).IsQuasicoherent)

/- Lemma 37.59.3 (2): for a locally finite type morphism, relative pseudo-coherence
implies membership in the derived quasi-coherent module property. -/
@[stacks 0CSU] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsPseudoCoherentOver.derivedQuasiCoherentModuleProperty :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
      {E : RingedSpace.ModuleDerived X.toRingedSpace},
      Scheme.ModuleDerived.IsPseudoCoherentOver f E →
        Scheme.derivedQuasiCoherentModuleProperty X E)
