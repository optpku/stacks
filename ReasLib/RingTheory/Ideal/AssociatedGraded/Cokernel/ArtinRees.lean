/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Filtration.ArtinRees.LinearMap
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Module
import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated graded cokernels under Artin--Rees perturbations

This leaf owns the explicit degreewise comparison between the associated
graded modules of two cokernels.  The construction uses a common quotient
presentation inside `I ^ n N`; its public endpoint is a degree-preserving
linear equivalence over `Ideal.AssociatedGraded.ring I`.

@stack 07VF
-/

@[expose] public section

open scoped DirectSum Pointwise
open LinearMap

universe u v w x

noncomputable section

namespace Ideal.AssociatedGraded.Cokernel

variable {A : Type u} [CommRing A]
variable {L : Type v} [AddCommGroup L] [Module A L]
variable {M : Type w} [AddCommGroup M] [Module A M]
variable {N : Type x} [AddCommGroup N] [Module A N]

/-- The denominator in the ambient `I ^ n N` presentation of the degree-`n`
associated graded piece of `N ⧸ LinearMap.range g`. -/
@[stacks 07VF "denominator of an associated-graded cokernel piece"]
abbrev denominator (I : Ideal A) (g : M →ₗ[A] N) (n : ℕ) :
    Submodule A (stage I N n) :=
  Submodule.comap (stage I N n).subtype
    (stage I N (n + 1) ⊔ LinearMap.range g ⊓ stage I N n)

/-- The quotient map `N → N ⧸ LinearMap.range g` sends the degree-`n`
filtration stage into the corresponding stage of the cokernel. -/
theorem stageMap_mem (I : Ideal A) (g : M →ₗ[A] N) (n : ℕ) (z : stage I N n) :
    (LinearMap.range g).mkQ z.1 ∈ stage I (N ⧸ LinearMap.range g) n := sorry

/-- The stage map induced by `N → N ⧸ LinearMap.range g`. -/
@[stacks 07VF "stage map to the cokernel filtration"]
def stageMap (I : Ideal A) (g : M →ₗ[A] N) (n : ℕ) :
    stage I N n →ₗ[A] stage I (N ⧸ LinearMap.range g) n :=
  LinearMap.codRestrict (stage I (N ⧸ LinearMap.range g) n)
    ((LinearMap.range g).mkQ.comp (stage I N n).subtype)
    (stageMap_mem I g n)

/-- The ambient-stage map to the degree-`n` associated graded piece of the
cokernel of `g`. -/
@[stacks 07VF "map to an associated-graded cokernel piece"]
def pieceMap (I : Ideal A) (g : M →ₗ[A] N) (n : ℕ) :
    stage I N n →ₗ[A] piece I (N ⧸ LinearMap.range g) n :=
  ((stage I (N ⧸ LinearMap.range g) (n + 1)).submoduleOf
      (stage I (N ⧸ LinearMap.range g) n)).mkQ.comp (stageMap I g n)

/-- The kernel of `pieceMap` is its explicit ambient denominator. -/
theorem pieceMap_ker (I : Ideal A) (g : M →ₗ[A] N) (n : ℕ) :
    LinearMap.ker (pieceMap I g n) = denominator I g n := sorry

/-- Every class in a cokernel's degree-`n` associated graded piece lifts
from the ambient stage `I ^ n N`. -/
theorem pieceMap_surjective (I : Ideal A) (g : M →ₗ[A] N) (n : ℕ) :
    Function.Surjective (pieceMap I g n) := sorry

/-- The explicit ambient quotient model of a cokernel's degree-`n`
associated graded piece. -/
@[stacks 07VF "ambient quotient model of a cokernel piece"]
def internalPieceEquiv (I : Ideal A) (g : M →ₗ[A] N) (n : ℕ) :
    (stage I N n ⧸ denominator I g n) ≃ₗ[A]
      piece I (N ⧸ LinearMap.range g) n :=
  (Submodule.quotEquivOfEq _ _ (pieceMap_ker I g n).symm).trans
    ((pieceMap I g n).quotKerEquivOfSurjective (pieceMap_surjective I g n))

/-- Congruent maps with a common Artin--Rees bound give the same ambient
denominator in every associated graded degree. -/
theorem denominator_eq_of_congr_mod_pow_and_artinRees
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (n : ℕ) :
    denominator I g n = denominator I g' n := sorry

/-- Lemma 15.4.2, degree `n`: an Artin--Rees perturbation induces a
canonical equivalence of the degree-`n` associated graded cokernel pieces. -/
@[stacks 07VF "degreewise associated graded cokernel equivalence"]
def pieceEquiv
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (n : ℕ) :
    piece I (N ⧸ LinearMap.range g) n ≃ₗ[A]
      piece I (N ⧸ LinearMap.range g') n :=
  (internalPieceEquiv I g n).symm.trans <|
    (Submodule.quotEquivOfEq _ _
      (denominator_eq_of_congr_mod_pow_and_artinRees
        I hf hg hexact hff' hgg' n)).trans <|
      internalPieceEquiv I g' n

/-- The direct-sum map assembled from the degreewise cokernel equivalences. -/
@[stacks 07VF "direct-sum associated-graded comparison map"]
def linearMap
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N)) :
    gradedModule I (N ⧸ LinearMap.range g) →ₗ[A]
      gradedModule I (N ⧸ LinearMap.range g') :=
  DirectSum.lmap fun n ↦ (pieceEquiv I hf hg hexact hff' hgg' n).toLinearMap

/-- The direct-sum map assembled from the inverse degreewise equivalences. -/
@[stacks 07VF "inverse direct-sum associated-graded comparison"]
def linearInvMap
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N)) :
    gradedModule I (N ⧸ LinearMap.range g') →ₗ[A]
      gradedModule I (N ⧸ LinearMap.range g) :=
  DirectSum.lmap fun n ↦ (pieceEquiv I hf hg hexact hff' hgg' n).symm.toLinearMap

/-- The inverse direct-sum map is a left inverse to the forward map. -/
theorem linearInvMap_comp_linearMap
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N)) :
    (linearInvMap I hf hg hexact hff' hgg').comp
      (linearMap I hf hg hexact hff' hgg') = LinearMap.id := sorry

/-- The inverse direct-sum map is a right inverse to the forward map. -/
theorem linearMap_comp_linearInvMap
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N)) :
    (linearMap I hf hg hexact hff' hgg').comp
      (linearInvMap I hf hg hexact hff' hgg') = LinearMap.id := sorry

/-- The underlying `A`-linear equivalence of the associated graded
cokernels, assembled degreewise. -/
@[stacks 07VF "underlying linear associated graded cokernel equivalence"]
def linearEquiv
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N)) :
    gradedModule I (N ⧸ LinearMap.range g) ≃ₗ[A]
      gradedModule I (N ⧸ LinearMap.range g') :=
  LinearEquiv.ofLinear
    (linearMap I hf hg hexact hff' hgg')
    (linearInvMap I hf hg hexact hff' hgg')
    (linearMap_comp_linearInvMap I hf hg hexact hff' hgg')
    (linearInvMap_comp_linearMap I hf hg hexact hff' hgg')

/-- The underlying linear equivalence acts on each direct-sum generator by
the corresponding degreewise equivalence. -/
@[stacks 07VF "degreewise action of the underlying cokernel equivalence"]
theorem linearEquiv_lof
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (n : ℕ) (z : piece I (N ⧸ LinearMap.range g) n) :
    linearEquiv I hf hg hexact hff' hgg'
        (DirectSum.lof A ℕ (piece I (N ⧸ LinearMap.range g)) n z) =
      DirectSum.lof A ℕ (piece I (N ⧸ LinearMap.range g')) n
        (pieceEquiv I hf hg hexact hff' hgg' n z) := sorry

/-- The direct-sum comparison commutes with the canonical action of
`Ideal.AssociatedGraded.ring I`. -/
theorem linearMap_map_smul
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (a : ring I) (z : gradedModule I (N ⧸ LinearMap.range g)) :
    linearMap I hf hg hexact hff' hgg' (a • z) =
      a • linearMap I hf hg hexact hff' hgg' z := sorry

/-- The inverse direct-sum comparison commutes with the canonical action of
`Ideal.AssociatedGraded.ring I`. -/
theorem linearInvMap_map_smul
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (a : ring I) (z : gradedModule I (N ⧸ LinearMap.range g')) :
    linearInvMap I hf hg hexact hff' hgg' (a • z) =
      a • linearInvMap I hf hg hexact hff' hgg' z := sorry

/-- The associated graded cokernel comparison as a linear map over
`Ideal.AssociatedGraded.ring I`. -/
@[stacks 07VF "associated-graded cokernel comparison map"]
def map
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N)) :
    gradedModule I (N ⧸ LinearMap.range g) →ₗ[ring I]
      gradedModule I (N ⧸ LinearMap.range g') where
  toFun := linearMap I hf hg hexact hff' hgg'
  map_add' := (linearMap I hf hg hexact hff' hgg').map_add
  map_smul' := linearMap_map_smul I hf hg hexact hff' hgg'

/-- The inverse associated graded cokernel comparison as a linear map over
`Ideal.AssociatedGraded.ring I`. -/
@[stacks 07VF "inverse associated-graded cokernel comparison"]
def invMap
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N)) :
    gradedModule I (N ⧸ LinearMap.range g') →ₗ[ring I]
      gradedModule I (N ⧸ LinearMap.range g) where
  toFun := linearInvMap I hf hg hexact hff' hgg'
  map_add' := (linearInvMap I hf hg hexact hff' hgg').map_add
  map_smul' := linearInvMap_map_smul I hf hg hexact hff' hgg'

/-- The forward `Gr_I(A)`-linear map followed by its inverse is the identity. -/
theorem map_comp_invMap
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N)) :
    (map I hf hg hexact hff' hgg').comp
      (invMap I hf hg hexact hff' hgg') = LinearMap.id := sorry

/-- The inverse `Gr_I(A)`-linear map followed by the forward map is the identity. -/
theorem invMap_comp_map
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N)) :
    (invMap I hf hg hexact hff' hgg').comp
      (map I hf hg hexact hff' hgg') = LinearMap.id := sorry

/-- Lemma 15.4.2: an Artin--Rees perturbation induces a degree-preserving
`Gr_I(A)`-linear equivalence between the associated graded cokernels. -/
@[stacks 07VF "associated graded cokernel equivalence"]
def equiv
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N)) :
    gradedModule I (N ⧸ LinearMap.range g) ≃ₗ[ring I]
      gradedModule I (N ⧸ LinearMap.range g') :=
  LinearEquiv.ofLinear
    (map I hf hg hexact hff' hgg')
    (invMap I hf hg hexact hff' hgg')
    (map_comp_invMap I hf hg hexact hff' hgg')
    (invMap_comp_map I hf hg hexact hff' hgg')

/-- The `Gr_I(A)`-linear equivalence acts degreewise on direct-sum
generators. -/
@[stacks 07VF "graded action of the associated graded cokernel equivalence"]
theorem equiv_lof
    (I : Ideal A) {c : ℕ} {f f' : L →ₗ[A] M} {g g' : M →ₗ[A] N}
    (hf : f.IsArtinReesBound I c) (hg : g.IsArtinReesBound I c)
    (hexact : Function.Exact f g)
    (hff' : LinearMap.range (f' - f) ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g' - g) ≤ I ^ (c + 1) • (⊤ : Submodule A N))
    (n : ℕ) (z : piece I (N ⧸ LinearMap.range g) n) :
    equiv I hf hg hexact hff' hgg'
        (DirectSum.lof A ℕ (piece I (N ⧸ LinearMap.range g)) n z) =
      DirectSum.lof A ℕ (piece I (N ⧸ LinearMap.range g')) n
        (pieceEquiv I hf hg hexact hff' hgg' n z) := sorry

end Ideal.AssociatedGraded.Cokernel
