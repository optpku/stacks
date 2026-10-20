/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Point
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-! Remark 21.39.13 (09CZ), constant-coefficient factorization.

Given a morphism from a chaotic-site ring sheaf to the constant sheaf associated
to a ring `B`, the reusable construction is the composition
`RingedSite.Hom.DerivedPoint.Chaotic.Constant.functor`: derived pullback to the constant `B`-sheaf,
the explicit constant-module presentation, and the derived point colimit. The comparison with the
additive lower shriek is owned by `RingedSite.Hom.DerivedPoint.Chaotic.Constant.factorization`;
after the comparison, `ModuleCat.forgetDerived` removes the `B`-module structure. The `Comm`
namespace is a specialization, not an assumption of the source statement.
-/

@[stacks 09CZ "derived lower shriek through module presheaves"]
#check @RingedSite.Hom.DerivedPoint.Chaotic.Constant.functor

@[stacks 09CZ "additive lower shriek factors through modules"]
#check @RingedSite.Hom.DerivedPoint.Chaotic.Constant.factorization

@[stacks 09CZ "chaotic constant-coefficient triangulated functor"]
#check @RingedSite.Hom.DerivedPoint.Chaotic.Constant.functor.hasTriangulatedStructure

#check @RingedSite.Hom.DerivedPoint.Chaotic.Constant.Comm.functor
#check @RingedSite.Hom.DerivedPoint.Chaotic.Constant.Comm.factorization
