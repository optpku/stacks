/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.Subcomplex.MissingSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
@stack 018R

# Adjoining one simplex to a simplicial subset

This file packages the canonical boundary map associated to a missing nondegenerate simplex and
the resulting pushout criterion. The construction is owned by the missing-simplex datum
`SSet.Subcomplex.N`, independently of any chapter-level filtration argument.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace SSet.Subcomplex.N

variable {V : SSet.{u}} {U : V.Subcomplex} (x : U.N)

/-- The canonical map from the boundary of a missing simplex to the old subcomplex. -/
@[stacks 018R "boundary map for a simplex attachment"]
def boundaryMap (hboundary : x.boundaryRangeLE) : ∂Δ[x.dim].toSSet ⟶ U.toSSet :=
  U.lift (∂Δ[x.dim].ι ≫ yonedaEquiv.symm x.simplex) hboundary

/-- Composing the boundary map with the subcomplex inclusion recovers the classified boundary. -/
@[reassoc, stacks 018R, stacks 018S "boundary-map compatibility for a simplex attachment"]
theorem boundaryMap.comp (hboundary : x.boundaryRangeLE) :
    x.boundaryMap hboundary ≫ U.ι =
      ∂Δ[x.dim].ι ≫ yonedaEquiv.symm x.simplex := sorry

/-- Lemma 14.21.7 (018R): adjoining one missing nondegenerate simplex whose boundary lies in the
old subcomplex gives the canonical simplex-boundary pushout square. -/
@[stacks 018R "single-simplex attachment pushout"]
theorem boundaryMap.isPushout (hboundary : x.boundaryRangeLE)
    (hgen : U ⊔ Subcomplex.ofSimplex x.simplex = ⊤) :
    IsPushout ∂Δ[x.dim].ι (x.boundaryMap hboundary)
      (yonedaEquiv.symm x.simplex) U.ι := sorry

end SSet.Subcomplex.N

namespace SSet.Subcomplex.singleSimplex

variable {V : SSet.{u}} {U W : V.Subcomplex}

/-- Lemma 14.21.7 (018R): the degreewise conditions saying that `V` is obtained from `U` by
adjoining the simplex `x` in degree `n`, with every higher missing simplex degenerate. -/
@[stacks 018R "degreewise conditions for adjoining one simplex"]
structure Degreewise (U : V.Subcomplex) (n : ℕ) (x : V _⦋n⦌) : Prop where
  /-- The simplex being adjoined does not already belong to the subcomplex. -/
  notMem : x ∉ U.obj _
  /-- Below degree `n`, the subcomplex already contains every simplex. -/
  eq_top_of_lt : ∀ i, i < n → U.obj (op ⦋i⦌) = Set.univ
  /-- In degree `n`, adjoining `x` exhausts all simplices. -/
  obj_union_singleton : U.obj (op ⦋n⦌) ∪ {x} = Set.univ
  /-- Above degree `n`, every simplex outside the subcomplex is degenerate. -/
  degenerate_of_lt : ∀ {j}, n < j → ∀ z : V _⦋j⦌,
    z ∉ U.obj _ → z ∈ V.degenerate j

namespace Degreewise

/-- The four defining conditions of a degreewise single-simplex extension. -/
@[stacks 018R "specification of the degreewise single-simplex conditions"]
theorem spec {n : ℕ} {x : V _⦋n⦌} (h : Degreewise U n x) :
    x ∉ U.obj _ ∧
      (∀ i, i < n → U.obj (op ⦋i⦌) = Set.univ) ∧
      U.obj (op ⦋n⦌) ∪ {x} = Set.univ ∧
      ∀ {j}, n < j → ∀ z : V _⦋j⦌,
        z ∉ U.obj _ → z ∈ V.degenerate j := sorry

/-- The distinguished simplex in a degreewise single-simplex extension is nondegenerate. -/
@[stacks 018R "the adjoined simplex is nondegenerate"]
theorem nonDegenerate {n : ℕ} {x : V _⦋n⦌} (h : Degreewise U n x) :
    x ∈ V.nonDegenerate n := sorry

/-- The explicit missing nondegenerate simplex determined by the degreewise conditions. -/
@[stacks 018R "missing nondegenerate simplex from degreewise conditions"]
def simplex {n : ℕ} {x : V _⦋n⦌} (h : Degreewise U n x) : U.N :=
  N.mk x h.nonDegenerate h.notMem

/-- The simplex underlying the explicit missing-simplex datum is the specified simplex `x`. -/
@[simp, stacks 018R "underlying simplex of the degreewise missing-simplex datum"]
theorem simplex_eq {n : ℕ} {x : V _⦋n⦌} (h : Degreewise U n x) :
    h.simplex.simplex = x := sorry

/-- The boundary of the distinguished simplex is contained in the old subcomplex. -/
@[stacks 018R "boundary condition from degreewise single-simplex data"]
theorem boundary {n : ℕ} {x : V _⦋n⦌} (h : Degreewise U n x) :
    h.simplex.boundaryRangeLE := sorry

/-- Adjoining the distinguished simplex to the old subcomplex gives the whole simplicial set. -/
@[stacks 018R "generation by the degreewise distinguished simplex"]
theorem adjoin_eq_top {n : ℕ} {x : V _⦋n⦌} (h : Degreewise U n x) :
    U ⊔ Subcomplex.ofSimplex h.simplex.simplex = ⊤ := sorry

end Degreewise

/-- A single-simplex attachment from `U` to `W`, retaining the missing nondegenerate simplex,
its boundary condition, and the resulting join equality as reusable data. -/
@[stacks 018S "single-simplex attachment"]
structure Attachment (U W : V.Subcomplex) where
  /-- The nondegenerate simplex missing from the source subcomplex. -/
  simplex : U.N
  /-- The boundary of the attached simplex already lies in the source subcomplex. -/
  boundary : simplex.boundaryRangeLE
  /-- Adjoining the simplex to the source gives the target subcomplex. -/
  adjoin_eq : U ⊔ Subcomplex.ofSimplex simplex.simplex = W

namespace Attachment

/-- Build an attachment from a specified missing simplex, its boundary condition, and the
equality identifying the target with the resulting join. -/
@[stacks 018S "attachment from a missing simplex"]
def ofSimplex (x : U.N) (boundary : x.boundaryRangeLE)
    (adjoin_eq : U ⊔ Subcomplex.ofSimplex x.simplex = W) : Attachment U W where
  simplex := x
  boundary := boundary
  adjoin_eq := adjoin_eq

/-- The canonical attachment obtained by adjoining a specified missing simplex. -/
@[stacks 018S "canonical attachment adjoining a missing simplex"]
def adjoin (x : U.N) (boundary : x.boundaryRangeLE) :
    Attachment U (U ⊔ Subcomplex.ofSimplex x.simplex) :=
  ofSimplex x boundary rfl

/-- The defining boundary and join conditions of a single-simplex attachment. -/
@[stacks 018S "specification of a single-simplex attachment"]
theorem spec (A : Attachment U W) :
    A.simplex.boundaryRangeLE ∧
      U ⊔ Subcomplex.ofSimplex A.simplex.simplex = W := sorry

/-- The source subcomplex of an attachment is contained in its target. -/
@[stacks 018S "source inclusion of a single-simplex attachment"]
theorem sourceLE (A : Attachment U W) : U ≤ W := sorry

/-- The simplex subcomplex of an attachment is contained in its target. -/
@[stacks 018S "attached simplex inclusion"]
theorem simplexLE (A : Attachment U W) :
    Subcomplex.ofSimplex A.simplex.simplex ≤ W := sorry

/-- The canonical boundary map of a single-simplex attachment. -/
@[stacks 018S "boundary map of a single-simplex attachment"]
def boundaryMap (A : Attachment U W) :
    ∂Δ[A.simplex.dim].toSSet ⟶ U.toSSet :=
  A.simplex.boundaryMap A.boundary

/-- The canonical inclusion of the source into the target of an attachment. -/
@[stacks 018S "source map of a single-simplex attachment"]
def sourceMap (A : Attachment U W) : U.toSSet ⟶ W.toSSet :=
  Subcomplex.homOfLE (le_sup_left.trans A.adjoin_eq.le)

/-- The canonical simplex map into the target of an attachment. -/
@[stacks 018S "simplex map of a single-simplex attachment"]
def simplexMap (A : Attachment U W) : Δ[A.simplex.dim] ⟶ W.toSSet :=
  Subcomplex.toOfSimplex A.simplex.simplex ≫
    Subcomplex.homOfLE (le_sup_right.trans A.adjoin_eq.le)

/-- The boundary square associated to an attachment commutes. -/
@[reassoc, stacks 018R, stacks 018S "boundary square of a single-simplex attachment"]
theorem boundaryMap_comp (A : Attachment U W) :
    ∂Δ[A.simplex.dim].ι ≫ A.simplexMap =
      A.boundaryMap ≫ A.sourceMap := sorry

/-- A single-simplex attachment is the pushout of its boundary inclusion. -/
@[stacks 018R "single-simplex attachment pushout with specified target"]
theorem isPushout (A : Attachment U W) :
    IsPushout ∂Δ[A.simplex.dim].ι A.boundaryMap
      A.simplexMap A.sourceMap := sorry

end Attachment

namespace Degreewise

/-- The explicit canonical attachment to the full subcomplex determined by the degreewise
single-simplex conditions. -/
@[stacks 018R "attachment from degreewise single-simplex conditions"]
def attachment {n : ℕ} {x : V _⦋n⦌} (h : Degreewise U n x) : Attachment U ⊤ where
  simplex := h.simplex
  boundary := h.boundary
  adjoin_eq := h.adjoin_eq_top

/-- Lemma 14.21.7 (018R): the degreewise single-simplex conditions exhibit `V` as the pushout of
the boundary inclusion along the map classifying `x`. -/
@[stacks 018R]
theorem isPushout {n : ℕ} {x : V _⦋n⦌} (h : Degreewise U n x) :
    IsPushout ∂Δ[n].ι (h.simplex.boundaryMap h.boundary)
      (yonedaEquiv.symm x) U.ι := sorry

end Degreewise

end SSet.Subcomplex.singleSimplex
