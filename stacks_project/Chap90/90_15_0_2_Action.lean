/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import stacks_project.Chap90.«90_15_0_1_TangentSpace»
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass

/-!
# Derivation Λ k k-action on tangent spaces

A derivation `D : Derivation Λ k k` determines the dual-number automorphism `f_{1,D}` sending
`a + v ε` to `a + (v + D a) ε`. Restriction along `R → k` yields an action on
`Derivation Λ R k`, and cofibered pushforward along that automorphism acts on
`Functor.tangentSpace p`.
-/

@[expose] public section

open CategoryTheory TrivSqZeroExt
open Functor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

noncomputable section

namespace DualNumber

/-- The dual-number automorphism `f_{1,D}` sending `a + vε` to `a + (v + D a)ε`. -/
def autOfDerivation (D : Derivation Λ k k) : DualNumber k →ₐ[Λ] DualNumber k where
  toFun x := inl x.fst + inr (x.snd + D x.fst)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- `autOfDerivation D` evaluates to `inl x.fst + inr (x.snd + D x.fst)`. -/
theorem autOfDerivation_apply (D : Derivation Λ k k) (x : DualNumber k) :
    autOfDerivation D x = inl x.fst + inr (x.snd + D x.fst) := sorry

end DualNumber

namespace ArtinianLocalAlgCat

/-- The morphism of `C_Λ` associated to `DualNumber.autOfDerivation D`. -/
def dualNumberAut (D : Derivation Λ k k) : dualNumber Λ k ⟶ dualNumber Λ k where
  hom := DualNumber.autOfDerivation D
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `dualNumberAut D` is `DualNumber.autOfDerivation D`. -/
theorem dualNumberAut_hom (D : Derivation Λ k k) :
    (dualNumberAut D).hom = DualNumber.autOfDerivation D := sorry

end ArtinianLocalAlgCat

section DerivationAction

variable {R : Type u} [CommRing R] [Algebra Λ R] [Algebra R k] [IsScalarTower Λ R k]

/-- The additive action of `Derivation Λ k k` on `Derivation Λ R k` by restriction along
`R → k`. -/
instance instAddAction_derivation : AddAction (Derivation Λ k k) (Derivation Λ R k) where
  vadd D D' := D' + D.compAlgebraMap R
  add_vadd := sorry
  zero_vadd := sorry

/-- The action of a residue derivation on an `R`-derivation is addition of its restriction. -/
theorem vadd_eq (D : Derivation Λ k k) (D' : Derivation Λ R k) :
    D +ᵥ D' = D' + D.compAlgebraMap R := sorry

end DerivationAction

variable {F : Type v} [Category.{v} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

/-- Predeformation categories are cofibered in groupoids, so `p.op` is fibered in groupoids. -/
instance instIsFiberedInGroupoids_op (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsPredeformationCategory p] : IsFibered.InGroupoids p.op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- Pushforward along `ArtinianLocalAlgCat.dualNumberAut D` acts on the tangent space of a
predeformation category. -/
instance instAddAction_tangentSpace [IsPredeformationCategory p] :
    AddAction (Derivation Λ k k) (tangentSpace p) where
  vadd D :=
    (pushforwardFiberFunctor p (cleavageOp p) (ArtinianLocalAlgCat.dualNumberAut D)).isoClassesMap
  add_vadd := sorry
  zero_vadd := sorry

/-- The tangent-space action of `D` is the isomorphism-class map of pushforward along
`ArtinianLocalAlgCat.dualNumberAut D`. -/
theorem vadd_tangentSpace [IsPredeformationCategory p] (D : Derivation Λ k k)
    (x : tangentSpace p) :
    D +ᵥ x =
      (pushforwardFiberFunctor p (cleavageOp p)
        (ArtinianLocalAlgCat.dualNumberAut D)).isoClassesMap x := sorry

end CategoryTheory.Functor

namespace FormalObject

/-- The differential of a formal object is equivariant for the `Derivation Λ k k`-actions. -/
theorem differential_vadd (ξ : FormalObject p) [IsPredeformationCategory p]
    (D : Derivation Λ k k) (D' : Derivation Λ ξ.base.carrier k) :
    differential ξ (D +ᵥ D') = D +ᵥ differential ξ D' := sorry

end FormalObject

end
