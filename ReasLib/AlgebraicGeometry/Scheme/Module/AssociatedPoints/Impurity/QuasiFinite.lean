/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity.FinitePresentation
import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.GenericPoints
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.GenericFiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.ClosedSubscheme

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Impurity

/-- Over a locally Noetherian scheme, the existence of an impurity above a point implies
the existence of one whose base-change morphism is finite type and quasi-finite at its
special point. -/
@[stacks 05J1]
theorem exists_quasiFiniteAt {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
    [Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    [IsLocallyNoetherian S] (s : S) (h_impurity : Nonempty (Impurity F f s)) :
    ∃ I : Impurity F f s, Hom.FiniteType.QuasiFiniteAt I.g I.specialPoint := sorry

end AlgebraicGeometry.Scheme.Modules.Impurity
