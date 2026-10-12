/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.Splitting.LowerFace
public import Mathlib.Algebra.Category.Grp.Abelian
import StacksCheckRecall

/-!
@stack 017U

# Lemma 14.18.5 compatibility facade

The reusable owner is the lower-face Dold--Kan splitting functor for an arbitrary abelian
category.  This file records its specialization to simplicial abelian groups.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicTopology
open scoped Simplicial

noncomputable section

namespace CategoryTheory.SimplicialObject

variable (U : SimplicialObject AddCommGrpCat) (n : ℕ) (Δ : SimplexCategoryᵒᵖ)

/- Lemma 14.18.5 (1): in degree zero the lower-face normalized summand is the whole object. -/
@[stacks 017U "Lemma 14.18.5 (1)"]
#check (normalizedMoore.lowerFace.subobject.zero U :
  normalizedMoore.lowerFace.subobject U 0 = ⊤)

/- Lemma 14.18.5 (2): in positive degree the summand is the intersection of the kernels of
`d₀, ..., dₙ`. -/
@[stacks 017U "Lemma 14.18.5 (2)"]
#check (normalizedMoore.lowerFace.subobject.add_one U n :
  normalizedMoore.lowerFace.subobject U (n + 1) =
    Finset.univ.inf (fun k : Fin (n + 1) ↦
      kernelSubobject (U.δ (Fin.castSucc k))))

/- Lemma 14.18.5 (3): these summands give the canonical coproduct decomposition in every
simplicial degree. -/
@[stacks 017U "Lemma 14.18.5 (3)"]
#check (inferInstance : IsIso (normalizedMoore.lowerFace.decomposition U Δ))

/- Lemma 14.18.5 (4): the source-convention splitting is functorial. -/
@[stacks 017U "Lemma 14.18.5 (4)"]
#check (normalizedMoore.lowerFace.splitting.functor (A := AddCommGrpCat) :
  SimplicialObject AddCommGrpCat ⥤ Split AddCommGrpCat)

/- The canonical lower-face owner also exposes the source-level splitness witness directly. -/
#check normalizedMoore.lowerFace.splitting.isSplit U

/- The coproduct decomposition and its naturality are inherited from the generic split-object
owner, so downstream arguments can import that API without importing this chapter facade. -/
#check (Split.decomposition.natIso AddCommGrpCat Δ :
  Split.source.functor AddCommGrpCat Δ ≅
    Split.forget AddCommGrpCat ⋙ (evaluation SimplexCategoryᵒᵖ AddCommGrpCat).obj Δ)

end CategoryTheory.SimplicialObject
