/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.«90_15_0_2_Action»

/-!
# Derivation action on the tangent space of a predeformation category

A derivation `D : Derivation Λ k k` determines the dual-number automorphism `f_{1,D}` of
`ArtinianLocalAlgCat.dualNumber Λ k` already owned as `ArtinianLocalAlgCat.dualNumberAut D`.
The named map `a` of the source is cofibered pushforward of dual-number fibre objects along
that automorphism, acting on `Functor.tangentSpace`.
-/

@[expose] public section

open CategoryTheory
open Functor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

noncomputable section

namespace ArtinianLocalAlgCat

/-- The automorphism `f_{1,D}` of `dualNumber Λ k` in `C_Λ`, with inverse `f_{1,-D}`. -/
def dualNumberAutIso (D : Derivation Λ k k) : dualNumber Λ k ≅ dualNumber Λ k where
  hom := dualNumberAut D
  inv := dualNumberAut (-D)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying morphism of `dualNumberAutIso D` is `dualNumberAut D`. -/
theorem dualNumberAutIso_hom (D : Derivation Λ k k) :
    (dualNumberAutIso D).hom = dualNumberAut D := sorry

/-- The inverse of `dualNumberAutIso D` is `dualNumberAut (-D)`. -/
theorem dualNumberAutIso_inv (D : Derivation Λ k k) :
    (dualNumberAutIso D).inv = dualNumberAut (-D) := sorry

/-- The dual-number automorphism associated to the zero derivation is the identity of
`dualNumber Λ k`. -/
theorem dualNumberAut_zero :
    dualNumberAut (0 : Derivation Λ k k) = 𝟙 (dualNumber Λ k) := sorry

/-- Composition of dual-number automorphisms adds the corresponding derivations:
`f_{1,D} ∘ f_{1,D'} = f_{1, D + D'}`. -/
theorem dualNumberAut_add (D D' : Derivation Λ k k) :
    dualNumberAut D' ≫ dualNumberAut D = dualNumberAut (D + D') := sorry

end ArtinianLocalAlgCat

variable {F : Type v} [Category.{v} F]

namespace CategoryTheory.Functor

/-- The action of a `Λ`-derivation of `k` on the tangent space of a predeformation category:
`derivationAction p D` is the map on isomorphism classes induced by cofibered pushforward
along `ArtinianLocalAlgCat.dualNumberAut D`. -/
def derivationAction (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsPredeformationCategory p]
    (D : Derivation Λ k k) : tangentSpace p → tangentSpace p :=
  (pushforwardFiberFunctor p (cleavageOp p) (ArtinianLocalAlgCat.dualNumberAut D)).isoClassesMap

/-- On a represented class, the action is the isomorphism class of the chosen pushforward of
the fibre representative. -/
theorem derivationAction_mk (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsPredeformationCategory p]
    (D : Derivation Λ k k) (x : p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k)) :
    derivationAction p D (tangentSpace.mk p x) =
      tangentSpace.mk p
        (pushforwardFiberObj p (cleavageOp p) (ArtinianLocalAlgCat.dualNumberAut D) x) :=
  sorry

/-- The named action agrees with the existing `AddAction` of `Derivation Λ k k` on
`tangentSpace p`. -/
theorem derivationAction_vadd (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsPredeformationCategory p]
    (D : Derivation Λ k k) (x : tangentSpace p) :
    derivationAction p D x = D +ᵥ x := sorry

/-- The zero derivation acts as the identity on the tangent space. -/
theorem derivationAction_zero (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsPredeformationCategory p] :
    derivationAction p 0 = id := sorry

/-- The action is additive in the derivation: `a(D + D') = a(D) ∘ a(D')`. -/
theorem derivationAction_add (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsPredeformationCategory p]
    (D D' : Derivation Λ k k) :
    derivationAction p (D + D') = derivationAction p D ∘ derivationAction p D' := sorry

end CategoryTheory.Functor

end
