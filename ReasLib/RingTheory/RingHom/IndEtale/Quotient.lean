/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.IndEtale.BaseChange

@[expose] public section

/-!
# Quotients of ind-etale ring maps

@stack 05WQ

This leaf records quotient compatibility at the representation-level
`RingHom.IndEtale.Raw` owner.  Keeping the raw presentation universe explicit
preserves the generality needed by categorical filtered-colimit arguments.
-/

universe u

namespace RingHom.IndEtale.Raw

/-- Tag `05WQ`: quotienting an ind-etale algebra map by a source ideal and
its image ideal preserves its same-universe raw ind-etale presentation. -/
@[stacks 05WQ "ind-etale quotient"]
theorem quotient {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A)
    (h : RingHom.IndEtale.Raw.{u, u, u} (algebraMap A B)) :
    RingHom.IndEtale.Raw.{u, u, u}
      (algebraMap (A ⧸ I) (B ⧸ Ideal.map (algebraMap A B) I)) := sorry

end RingHom.IndEtale.Raw
