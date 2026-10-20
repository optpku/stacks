/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.GroupRepresentation.Hull
import StacksCheckRecall

/-!
# Hull and prorepresentability of isomorphism classes of group representations

In Example 93.5.1, if `Γ` is finitely generated and `Λ` is classical, the functor of
isomorphism classes of objects of `Def_{V, ρ0}` has a hull. If in addition
`H^0(Γ, End_k(V)) = k`, that functor is prorepresentable.
-/

@[expose] public section

open CategoryTheory Functor

noncomputable section

universe u

variable (Γ Λ k : Type u) [Group Γ] [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k]
variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]

variable (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
variable [Group.FG Γ] [ArtinianLocalAlgCat.IsClassical Λ k]

/- Lemma 93.5.4 (1)
In Example 93.5.1 assume `Γ` is finitely generated. Let
`ρ0 : Γ →* LinearMap.GeneralLinearGroup k V` be a finite-dimensional representation.
Assume `Λ` is a complete local ring with residue field `k` (the classical case).
Then the functor sending `A` to the isomorphism classes of objects of
`Def_{V, ρ0}(A)`, i.e. `F(A) = Ob(Def_{V, ρ0}(A))/≅`, has a hull. -/
@[stacks 0ET1] #check (GroupRepCat.exists_isHull_isoClass Γ Λ k ρ0 :
    ∃ R : CompleteLocalAlgCat Λ k,
      ∃ η : CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ⟶
          GroupRepCat.isoClassFunctor Γ Λ k ρ0,
        NatTrans.IsSmooth η ∧
          Function.Bijective (η.app (ArtinianLocalAlgCat.dualNumber Λ k)))

/- Lemma 93.5.4 (2)
If in addition `H^0(Γ, End_k(V)) = k`, recorded as
`Module.finrank k (endRepresentation Γ Λ k ρ0).invariants = 1`, then the functor of
isomorphism classes is prorepresentable. -/
@[stacks 0ET1] #check (GroupRepCat.isProrepresentable_isoClass Γ Λ k ρ0 :
    Module.finrank k (GroupRepCat.endRepresentation Γ Λ k ρ0).invariants = 1 →
    ∃ R : CompleteLocalAlgCat Λ k,
      Nonempty
        (CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ≅
          GroupRepCat.isoClassFunctor Γ Λ k ρ0))

#check (CategoryTheory.Functor.fiberIsoClassFunctor.obj
    (GroupRepCat.deformationForget Γ Λ k ρ0) :
  ∀ A : ArtinianLocalAlgCat Λ k,
    (GroupRepCat.isoClassFunctor Γ Λ k ρ0).obj A =
      isomorphismClasses.obj (Cat.of ((GroupRepCat.deformationForget Γ Λ k ρ0).Fiber A)))

