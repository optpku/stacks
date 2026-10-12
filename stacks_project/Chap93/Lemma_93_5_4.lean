/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap90.Definition_90_3_1_Classical
public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
public import stacks_project.Chap90.Definition_90_23_1_Smooth
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass
public import stacks_project.Chap93.Lemma_93_5_3

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

namespace GroupRepCat

variable (Γ Λ k : Type u) [Group Γ] [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k]
variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- The functor of isomorphism classes of objects of `Def_{V, ρ0}`. -/
abbrev isoClassFunctor (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    ArtinianLocalAlgCat Λ k ⥤ Type (u + 1) :=
  fiberIsoClassFunctor (deformationForget Γ Λ k ρ0)

/-- The value of `isoClassFunctor ρ0` at `A` is the type of isomorphism classes of objects
of `(deformationForget Γ Λ k ρ0).Fiber A`. -/
theorem isoClassFunctor_obj (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (A : ArtinianLocalAlgCat Λ k) :
    (isoClassFunctor Γ Λ k ρ0).obj A =
      isomorphismClasses.obj (Cat.of ((deformationForget Γ Λ k ρ0).Fiber A)) :=
  sorry

/-- Lemma 93.5.4 (1)
In Example 93.5.1 assume `Γ` is finitely generated. Let
`ρ0 : Γ →* LinearMap.GeneralLinearGroup k V` be a finite-dimensional representation.
Assume `Λ` is a complete local ring with residue field `k` (the classical case).
Then the functor sending `A` to the isomorphism classes of objects of
`Def_{V, ρ0}(A)`, i.e. `F(A) = Ob(Def_{V, ρ0}(A))/≅`, has a hull. -/
@[stacks 0ET1]
theorem exists_isHull_isoClass (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    [Group.FG Γ] [ArtinianLocalAlgCat.IsClassical Λ k] :
    ∃ R : CompleteLocalAlgCat Λ k,
      ∃ η : CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ⟶
          isoClassFunctor Γ Λ k ρ0,
        NatTrans.IsSmooth η ∧
          Function.Bijective (η.app (ArtinianLocalAlgCat.dualNumber Λ k)) :=
  sorry

/-- Lemma 93.5.4 (2)
If in addition `H^0(Γ, End_k(V)) = k`, recorded as
`Module.finrank k (endRepresentation Γ Λ k ρ0).invariants = 1`, then the functor of
isomorphism classes is prorepresentable. -/
@[stacks 0ET1]
theorem isProrepresentable_isoClass (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    [Group.FG Γ] [ArtinianLocalAlgCat.IsClassical Λ k]
    (hH0 : Module.finrank k (endRepresentation Γ Λ k ρ0).invariants = 1) :
    ∃ R : CompleteLocalAlgCat Λ k,
      Nonempty
        (CompleteLocalAlgCat.restrictedCoyoneda R ⋙ uliftFunctor.{u + 1, u} ≅
          isoClassFunctor Γ Λ k ρ0) :=
  sorry

end GroupRepCat
