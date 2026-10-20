/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Derived
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.KInjective.RightDerived
import StacksCheckRecall

@[expose] public section

/-!
# Definition 24.29.2

The algebraic DG-module library owns derived fixed-source internal Hom.  Independently, the
intrinsic sheaf-DG K-injective API owns total right derivation for any exact homotopy-level
functor, hence also the derived pushforward once its concrete underived functor is supplied.

The concrete ringed-site internal-Hom and pushforward functors are not yet modeled as shared
owners; these checks deliberately expose that remaining specialization boundary instead of
installing chapter-local stand-ins.
-/

open SheafOfModules.RingedSite.DifferentialGradedModule

@[stacks 0FTP "derived internal Hom"]
#check @DifferentialGradedBimodule.InternalHom.derivedFunctor
#check @DifferentialGradedBimodule.InternalHom.derivedUnit

@[stacks 0FTP "derived pushforward"] #check @Functor.RightDerived.functor
#check @Functor.RightDerived.unit
#check @Functor.RightDerived.isRightDerived
