/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.Weakly.Colimit
public import ReasLib.RingTheory.RingHom.IndEtale.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ind-etale maps are weakly etale

The raw filtered-colimit presentation of an ind-etale ring map implies the canonical weakly-etale
property.

@stack 092N
-/

@[expose] public section

universe u v w

namespace RingHom.IndEtale.Raw

/-- An ind-etale algebra presented as a filtered colimit of etale algebras is weakly etale. -/
@[stacks 092N "ind-etale algebras are weakly etale"]
theorem weaklyEtale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (h : RingHom.IndEtale.Raw.{u, v, w} (algebraMap A B)) :
    Algebra.WeaklyEtale A B := sorry

end RingHom.IndEtale.Raw
