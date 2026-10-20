/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigEtale
public import ReasLib.RingTheory.AdicCompletion.RigSmooth

@[expose] public section

universe u

namespace Algebra.RigEtale

/-- A rig-étale algebra over a Noetherian ring is rig-smooth with respect to the
same ideal. -/
instance toRigSmooth {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : Type u} [CommRing B] [Algebra A B] [RigEtale I B] :
    RigSmooth I B := sorry

end Algebra.RigEtale
