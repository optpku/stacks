/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DualNumber.Derivation
public import ReasLib.RingTheory.Derivation.Action
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.Action
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Action
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Orbits

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

#check (DualNumber.autOfDerivation :
  Derivation Λ k k → DualNumber k →ₐ[Λ] DualNumber k)
#check (DualNumber.autOfDerivation_apply :
  ∀ (D : Derivation Λ k k) (value : DualNumber k),
    DualNumber.autOfDerivation D value = inl value.fst + inr (value.snd + D value.fst))
#check (ArtinianLocalAlgCat.dualNumberAut :
  Derivation Λ k k →
    (ArtinianLocalAlgCat.dualNumber Λ k ⟶ ArtinianLocalAlgCat.dualNumber Λ k))
#check (ArtinianLocalAlgCat.dualNumberAut_hom :
  ∀ D : Derivation Λ k k,
    (ArtinianLocalAlgCat.dualNumberAut D).hom = DualNumber.autOfDerivation D)

section DerivationAction

variable {R : Type u} [CommRing R] [Algebra Λ R] [Algebra R k] [IsScalarTower Λ R k]

#check (Derivation.instAddActionOfCompAlgebraMap :
  AddAction (Derivation Λ k k) (Derivation Λ R k))
#check (Derivation.vadd_eq_add_compAlgebraMap :
  ∀ (D : Derivation Λ k k) (baseDerivation : Derivation Λ R k),
    D +ᵥ baseDerivation = baseDerivation + D.compAlgebraMap R)

end DerivationAction

variable {F : Type v} [Category.{v} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

#check (Functor.instAddAction_tangentSpace :
  [Functor.IsPredeformationCategory p] → AddAction (Derivation Λ k k) (tangentSpace p))
#check (Functor.vadd_tangentSpace :
  [Functor.IsPredeformationCategory p] → ∀ (D : Derivation Λ k k) (value : tangentSpace p),
    D +ᵥ value =
      (pushforwardFiberFunctor p (cleavageOp p)
        (ArtinianLocalAlgCat.dualNumberAut D)).isoClassesMap value)
#check (FormalObject.differential_vadd :
  ∀ (ξ : FormalObject p) [Functor.IsPredeformationCategory p]
    (D : Derivation Λ k k) (baseDerivation : Derivation Λ ξ.base.carrier k),
    FormalObject.differential ξ (D +ᵥ baseDerivation) =
      D +ᵥ FormalObject.differential ξ baseDerivation)
