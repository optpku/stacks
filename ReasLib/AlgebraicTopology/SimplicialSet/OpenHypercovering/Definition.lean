module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import ReasLib.AlgebraicTopology.SimplicialSet.OpenHypercovering.Intersection

/-!
# Open hypercoverings

This module provides the data of a simplicial-indexed family of opens and the corresponding open
hypercovering condition.  The target is an arbitrary topological space; `TopCat` is only needed by
applications that turn the family into a simplicial topological space.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u v

namespace SSet

variable {X : Type u} [TopologicalSpace X]
variable {I J K : SSet.{v}}

/-- A family of opens indexed by a simplicial set, with simplicial operators inducing inclusions
from source opens into target opens. -/
@[stacks 01H1 "simplicial family of opens"]
structure OpenFamily (X : Type u) [TopologicalSpace X] (I : SSet.{v}) where
  /-- The open associated to an indexed simplex. -/
  openAt {Δ : SimplexCategoryᵒᵖ} : I.obj Δ → Opens X
  /-- A simplicial operator sends the open at a source index into the open at its target index. -/
  map_le {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') (i : I.obj Δ) :
    openAt i ≤ openAt (I.map f i)

namespace OpenFamily

/-- Build a simplicial family of opens from the face inclusions and degeneracy equalities appearing
in the source definition.  The generated simplex-category relations supply `map_le` for every
simplicial operator. -/
@[stacks 01H1 "open family from face and degeneracy conditions"]
def ofFaceDegeneracy
    (openAt : {Delta : SimplexCategoryᵒᵖ} → I.obj Delta → Opens X)
    (h_face : ∀ {n : ℕ} (a : Fin (n + 2))
      (i : I.obj (op <| SimplexCategory.mk (n + 1))),
        openAt i ≤ openAt (I.δ a i))
    (h_degeneracy : ∀ {n : ℕ} (a : Fin (n + 1))
      (i : I.obj (op <| SimplexCategory.mk n)),
        openAt (I.σ a i) = openAt i) :
    OpenFamily X I where
  openAt := openAt
  map_le := sorry

/-- A split simplicial operator preserves the associated open. -/
@[stacks 01H1 "split simplicial operators preserve indexed opens"]
theorem map_openAt_eq_of_comp_eq_id (U : OpenFamily X I)
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') (g : Δ' ⟶ Δ)
    (h : f ≫ g = 𝟙 Δ) (i : I.obj Δ) :
    U.openAt (I.map f i) = U.openAt i := sorry

/-- A face sends an indexed open into the open attached to that face. -/
@[stacks 01H1 "face inclusion for a simplicial family of opens"]
theorem face_le (U : OpenFamily X I) {n : ℕ} (a : Fin (n + 2))
    (i : I.obj (op <| SimplexCategory.mk (n + 1))) :
    U.openAt i ≤ U.openAt (I.δ a i) := sorry

/-- A degeneracy preserves the open attached to an indexed simplex. -/
@[simp, stacks 01H1 "degeneracy equality for a simplicial family of opens"]
theorem degeneracy_eq (U : OpenFamily X I) {n : ℕ} (a : Fin (n + 1))
    (i : I.obj (op <| SimplexCategory.mk n)) :
    U.openAt (I.σ a i) = U.openAt i := sorry

/-- A restricted open family inherits the inclusions induced by simplicial operators. -/
theorem restrict_map_le (U : OpenFamily X I) (f : J ⟶ I)
    {Δ Δ' : SimplexCategoryᵒᵖ} (g : Δ ⟶ Δ') (j : J.obj Δ) :
    U.openAt (f.app Δ j) ≤ U.openAt (f.app Δ' (J.map g j)) := sorry

/-- Restrict an indexed family of opens along a simplicial map of index sets. -/
def restrict (U : OpenFamily X I) (f : J ⟶ I) : OpenFamily X J where
  openAt j := U.openAt (f.app _ j)
  map_le g j := U.restrict_map_le f g j

/-- Restricting an open family computes pointwise by applying the index map. -/
@[simp] theorem restrict_openAt (U : OpenFamily X I) (f : J ⟶ I)
    {Δ : SimplexCategoryᵒᵖ} (j : J.obj Δ) :
    (U.restrict f).openAt j = U.openAt (f.app Δ j) := sorry

/-- Restriction of an open family along the identity map is the original family. -/
theorem restrict_id (U : OpenFamily X I) :
    U.restrict (𝟙 I) = U := sorry

/-- Restriction of an open family is compatible with composition of index maps. -/
theorem restrict_comp (U : OpenFamily X I) (f : J ⟶ I) (g : K ⟶ J) :
    U.restrict (g ≫ f) = (U.restrict f).restrict g := sorry

end OpenFamily

/-- A hypercovering of a topological space by a simplicial-indexed family of opens. -/
@[stacks 01H1 "open hypercovering data"]
structure OpenHypercovering (X : Type u) [TopologicalSpace X] where
  /-- The underlying simplicial set of indices. -/
  I : SSet.{v}
  /-- The open attached to every indexed simplex. -/
  family : OpenFamily X I
  /-- The degree-`0` opens cover the target space. -/
  zero_isOpenCover :
    TopologicalSpace.IsOpenCover
      (fun i : I.obj (op <| SimplexCategory.mk 0) ↦ family.openAt i)
  /-- Matching opens in degree `n + 1` cover every compatible prescribed degree-`n` intersection. -/
  succ (n : ℕ) :
    SSet.OpenHypercovering.BoundaryIntersection
      (fun i : I.obj (op <| SimplexCategory.mk n) ↦ family.openAt i)
      (fun j : I.obj (op <| SimplexCategory.mk (n + 1)) ↦ family.openAt j)

namespace OpenHypercovering

/-- The successor hypercovering condition as the covering equality for every compatible boundary
tuple. -/
@[stacks 01H4 "open-hypercovering successor covering equality"]
theorem succ.iInf_eq_iSup (H : OpenHypercovering.{u, v} X) (n : ℕ)
    (face : Fin (n + 2) → H.I.obj (op <| SimplexCategory.mk n))
    (hface : Boundary.Compatible H.I face) :
    (⨅ a, H.family.openAt (face a)) =
      iSup (fun j : MatchingIndices (fun a x ↦ H.I.δ a x) face ↦
        H.family.openAt j.1) := sorry

/-- The successor covering equality applied to a canonical compatible boundary tuple. -/
@[stacks 01H4 "open-hypercovering successor equality on a boundary tuple"]
theorem succ.iInf_eq_iSup_tuple (H : OpenHypercovering.{u, v} X) (n : ℕ)
    (t : Boundary.Tuple H.I (n := n)) :
    (⨅ a, H.family.openAt (t.face a)) =
      iSup (fun j : MatchingIndices (fun a x ↦ H.I.δ a x) t.face ↦
        H.family.openAt j.1) := sorry

/-- A matching open of an open hypercovering lies in every prescribed boundary open. -/
@[stacks 01H4 "matching open lies in every boundary open"]
theorem succ.matchingOpen_le (H : OpenHypercovering.{u, v} X) {n : ℕ}
    (face : Fin (n + 2) → H.I.obj (op <| SimplexCategory.mk n))
    (j : MatchingIndices (fun a x ↦ H.I.δ a x) face) (a : Fin (n + 2)) :
    H.family.openAt j.1 ≤ H.family.openAt (face a) := sorry

/-- Membership in a boundary intersection is witnessed by a matching open. -/
@[stacks 01H4 "membership in an open-hypercovering successor cover"]
theorem succ.mem_iInf_iff_exists (H : OpenHypercovering.{u, v} X) (n : ℕ)
    (face : Fin (n + 2) → H.I.obj (op <| SimplexCategory.mk n))
    (hface : Boundary.Compatible H.I face) (x : X) :
    x ∈ (⨅ a, H.family.openAt (face a) : Opens X) ↔
      ∃ j : MatchingIndices (fun a y ↦ H.I.δ a y) face,
        x ∈ H.family.openAt j.1 := sorry

/-- Membership in the successor cover, expressed for a canonical compatible boundary tuple. -/
@[stacks 01H4 "open-hypercovering successor membership on a boundary tuple"]
theorem succ.mem_iInf_iff_exists_tuple (H : OpenHypercovering.{u, v} X) (n : ℕ)
    (t : Boundary.Tuple H.I (n := n)) (x : X) :
    x ∈ (⨅ a, H.family.openAt (t.face a) : Opens X) ↔
      ∃ j : MatchingIndices (fun a y ↦ H.I.δ a y) t.face,
        x ∈ H.family.openAt j.1 := sorry

end OpenHypercovering

end SSet
