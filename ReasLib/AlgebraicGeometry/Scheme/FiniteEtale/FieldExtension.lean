/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Henselian
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- For a proper scheme over an algebraically closed field, base change along an
extension of algebraically closed fields induces an equivalence of categories
of finite étale schemes. -/
instance finiteEtaleBaseChangeIsEquivalenceOfAlgClosed
    {k k' : Type u} [Field k] [IsAlgClosed k] [Field k'] [Algebra k k']
    [IsAlgClosed k'] (X : SchemeOverField k) [IsProper X.hom] :
    Functor.IsEquivalence
      (Scheme.finiteEtaleBaseChange (FieldExtension.toSource k k' X.hom)) := sorry

end AlgebraicGeometry.SchemeOverField
