/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ContinuousRepresentation.Hull
import StacksCheckRecall

/-!
# Hull and prorepresentability of isomorphism classes of continuous representations

In Example 93.6.1, if `Γ` is topologically finitely generated and `Λ` is classical,
the functor of isomorphism classes of objects of `Def_{V, ρ0}` has a hull. If in
addition `H^0(Γ, End_k(V)) = k`, that functor is prorepresentable.
-/

@[expose] public section

open CategoryTheory Functor

noncomputable section

universe u

variable (Γ Λ k : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

variable (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
variable (hρ0 : ContinuousRep.IsContinuousDiscrete ρ0)
variable (hΓ : TopologicalGroup.IsFinitelyGenerated Γ)
variable [ArtinianLocalAlgCat.IsClassical Λ k]

/- Lemma 93.6.4 (1)
In Example 93.6.1 assume `Γ` is topologically finitely generated. Let
`ρ0 : Γ →* LinearMap.GeneralLinearGroup k V` be a finite-dimensional continuous
representation. Assume `Λ` is a complete local ring with residue field `k` (the
classical case). Then the functor sending `A` to the isomorphism classes of objects
of `Def_{V, ρ0}(A)`, i.e. `F(A) = Ob(Def_{V, ρ0}(A))/≅`, has a hull. -/
@[stacks 0ET2] #check (ContinuousRep.exists_isHull_isoClass Γ Λ k ρ0 hρ0 hΓ :
    ∃ R : CompleteLocalAlgCat Λ k,
      ∃ η : CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ⟶
          ContinuousRep.isoClassFunctor Γ Λ k ρ0 hρ0,
        NatTrans.IsSmooth η ∧
          Function.Bijective (η.app (ArtinianLocalAlgCat.dualNumber Λ k)))

/- Lemma 93.6.4 (2)
If in addition `H^0(Γ, End_k(V)) = k`, recorded as
`Module.finrank k (endRepresentation Γ Λ k ρ0 hρ0).invariants = 1`, then the functor
of isomorphism classes is prorepresentable. -/
@[stacks 0ET2] #check (ContinuousRep.isProrepresentable_isoClass Γ Λ k ρ0 hρ0 hΓ :
    Module.finrank k (ContinuousRep.endRepresentation Γ Λ k ρ0 hρ0).invariants = 1 →
    ∃ R : CompleteLocalAlgCat Λ k,
      Nonempty
        (CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ≅
          ContinuousRep.isoClassFunctor Γ Λ k ρ0 hρ0))

#check (CategoryTheory.Functor.fiberIsoClassFunctor.obj
    (ContinuousRep.deformationForget Γ Λ k ρ0 hρ0) :
  ∀ A : ArtinianLocalAlgCat Λ k,
    (ContinuousRep.isoClassFunctor Γ Λ k ρ0 hρ0).obj A =
      isomorphismClasses.obj
        (Cat.of ((ContinuousRep.deformationForget Γ Λ k ρ0 hρ0).Fiber A)))
