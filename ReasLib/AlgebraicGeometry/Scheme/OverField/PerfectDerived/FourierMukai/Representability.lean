/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.FourierMukai
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- Over a field, every linear fully faithful exact functor from the perfect derived
category of a smooth proper projective scheme to that of a smooth proper scheme is
isomorphic to the Fourier–Mukai transform of a perfect kernel on their fibre product. -/
theorem isPerfectFourierMukai_of_fullyFaithful
    {k : Type u} [Field k] (X Y : SchemeOverField k)
    [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom] [Smooth Y.hom]
    [HProjective X.hom]
    (F : PerfectDerived X ⥤ PerfectDerived Y)
    [F.Linear k] [F.Full] [F.Faithful]
    (hF_exact : F.HasTriangulatedStructure) :
    IsPerfectFourierMukai F :=
  sorry

end AlgebraicGeometry.SchemeOverField.PerfectDerived
