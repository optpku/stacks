/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.CostandardSimplex
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Pointwise
public import ReasLib.CategoryTheory.Limits.Shapes.Products.Reindex
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# Costandard powers and coskeleton projections

The costandard `k`-simplex indexes a simplicial power of an object `T`.  In degree `n + 1`,
the unit into the `n`-coskeleton forgets exactly the factors indexed by surjective maps
`[k] ⟶ [n + 1]`.  The target is therefore naturally the power indexed by nonsurjective maps,
and the unit is the corresponding product projection.
-/

@[expose] public section

open CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.CostandardPower

variable {C : Type u} [Category.{v} C]

/-- The maps indexing degree `q` of the power represented by the costandard `k`-simplex. -/
@[stacks 01GJ "costandard simplex-map indices"]
abbrev Index (k q : ℕ) := ⦋k⦌ ⟶ ⦋q⦌

/-- The boundary indices: simplex maps whose image omits at least one vertex. -/
@[stacks 01GJ "nonsurjective costandard indices"]
abbrev BoundaryIndex (k q : ℕ) :=
  {alpha : Index k q // ¬Function.Surjective alpha.toOrderHom}

/-- A costandard index is nonsurjective exactly when the corresponding simplex of the
standard simplex lies in its boundary. -/
@[stacks 01GJ "costandard boundary-index criterion"]
theorem mem_boundary_iff (alpha : Index k q) :
    SSet.stdSimplex.objEquiv.{w}.symm alpha ∈
        (SSet.boundary.{w} q).obj (op ⦋k⦌) ↔
      ¬Function.Surjective alpha.toOrderHom := sorry

/-- Nonsurjective costandard indices are canonically the simplices of the standard-simplex
boundary in the corresponding degree. -/
@[stacks 01GJ "costandard indices as boundary simplices"]
noncomputable def boundaryEquiv (k q : ℕ) :
    BoundaryIndex k q ≃ (SSet.boundary.{w} q).obj (op ⦋k⦌) :=
  SSet.stdSimplex.objEquiv.{w}.symm.subtypeEquiv
    (fun alpha ↦ (mem_boundary_iff.{w} alpha).symm)

/-- The boundary equivalence retains the underlying simplex map. -/
@[simp, stacks 01GJ "costandard boundary equivalence application"]
theorem boundaryEquiv_apply (alpha : BoundaryIndex k q) :
    SSet.stdSimplex.objEquiv.{w} (boundaryEquiv.{w} k q alpha).1 = alpha.1 := sorry

/-- The canonical inclusion of boundary indices into all costandard indices. -/
@[stacks 01GJ "boundary-index inclusion"]
def boundaryInclusion (k q : ℕ) : BoundaryIndex k q ↪ Index k q :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- The costandard simplex maps whose canonical image has dimension at most `n`. -/
@[stacks 01GJ "bounded-rank costandard indices"]
abbrev RankIndex (k n : ℕ) (q : SimplexCategory) :=
  { alpha : ⦋k⦌ ⟶ q // (image alpha).len ≤ n }

namespace RankIndex

/-- Postcomposition preserves the dimension bound on the canonical image. -/
@[stacks 01GJ "bounded-rank indices under postcomposition"]
theorem map_mem {k n : ℕ} {q r : SimplexCategory} (f : q ⟶ r)
    (alpha : RankIndex k n q) :
    (image (alpha.1 ≫ f)).len ≤ n := sorry

/-- Postcompose a bounded-rank costandard index. -/
@[stacks 01GJ "postcomposition of bounded-rank indices"]
def map {k n : ℕ} {q r : SimplexCategory} (f : q ⟶ r) :
    RankIndex k n q → RankIndex k n r :=
  fun alpha ↦ ⟨alpha.1 ≫ f, map_mem f alpha⟩

/-- Postcomposition does not change the underlying simplex-map formula. -/
@[simp, stacks 01GJ "bounded-rank postcomposition formula"]
theorem map_val {k n : ℕ} {q r : SimplexCategory} (f : q ⟶ r)
    (alpha : RankIndex k n q) :
    (map f alpha).1 = alpha.1 ≫ f := sorry

/-- Bounded-rank postcomposition by an identity is the identity. -/
@[stacks 01GJ "bounded-rank identity postcomposition"]
theorem map_id (k n : ℕ) (q : SimplexCategory) :
    TypeCat.ofHom (map (k := k) (n := n) (𝟙 q)) =
      𝟙 (RankIndex k n q) := sorry

/-- Bounded-rank postcomposition respects composition. -/
@[stacks 01GJ "bounded-rank composition postcomposition"]
theorem map_comp {k n : ℕ} {q r s : SimplexCategory}
    (f : q ⟶ r) (g : r ⟶ s) :
    TypeCat.ofHom (map (k := k) (n := n) (f ≫ g)) =
      TypeCat.ofHom (map f) ≫ TypeCat.ofHom (map g) := sorry

/-- Every index into an `n`-truncated simplex has image dimension at most `n`. -/
@[stacks 01GJ "bounded-rank indices in truncated degrees"]
theorem low_mem {k n : ℕ} (q : SimplexCategory.Truncated n)
    (alpha : ⦋k⦌ ⟶ q.obj) :
    (image alpha).len ≤ n := sorry

/-- Regard any costandard index into an `n`-truncated simplex as bounded-rank. -/
@[stacks 01GJ "costandard indices as bounded-rank indices"]
def low {k n : ℕ} (q : SimplexCategory.Truncated n) :
    (⦋k⦌ ⟶ q.obj) → RankIndex k n q.obj :=
  fun alpha ↦ ⟨alpha, low_mem q alpha⟩

/-- The canonical image of a bounded-rank index, bundled in the truncated simplex category. -/
@[stacks 01GJ "image simplex of a bounded-rank index"]
def imageObject {k n : ℕ} {q : SimplexCategory} (alpha : RankIndex k n q) :
    SimplexCategory.Truncated n :=
  ⟨image alpha.1, alpha.2⟩

end RankIndex

/-- Bounded-rank costandard indices form a covariant functor of the target simplex. -/
@[stacks 01GJ "bounded-rank costandard index functor"]
def rankIndexFunctor (k n : ℕ) : SimplexCategory ⥤ Type where
  obj q := RankIndex k n q
  map f := TypeCat.ofHom (RankIndex.map f)
  map_id q := RankIndex.map_id k n q
  map_comp f g := RankIndex.map_comp f g

/-- Every value of the bounded-rank costandard index functor is finite. -/
@[stacks 01GJ "finiteness of bounded-rank costandard indices"]
instance rankIndexFunctor.objFinite (k n : ℕ) :
    (rankIndexFunctor k n).ObjFinite := sorry

/-- The simplicial object whose degree `q` is the product of copies of `T` indexed by maps
`[k] ⟶ [q]`. -/
@[stacks 01GJ "costandard simplicial power"]
abbrev object [HasFiniteProducts C] (k : ℕ) (T : C) : SimplicialObject C :=
  Functor.indexedProd (coyoneda.obj (op ⦋k⦌))
    ((Functor.const SimplexCategoryᵒᵖ).obj T)

/-- Costandard simplicial power as a functor of the repeated object. -/
@[stacks 01GJ "costandard simplicial power functor"]
abbrev functor [HasFiniteProducts C] (k : ℕ) : C ⥤ SimplicialObject C :=
  Functor.const SimplexCategoryᵒᵖ ⋙
    Functor.indexedProd.functor (C := C) (coyoneda.obj (op ⦋k⦌))

/-- The simplicial power retaining exactly the costandard indices of image dimension at most
`n`. -/
@[stacks 01GJ "bounded-rank costandard simplicial power"]
abbrev rankObject [HasFiniteProducts C] (k n : ℕ) (T : C) : SimplicialObject C :=
  Functor.indexedProd (rankIndexFunctor k n)
    ((Functor.const SimplexCategoryᵒᵖ).obj T)

/-- The bounded-rank costandard power as a functor of the repeated object. -/
@[stacks 01GJ "bounded-rank costandard power functor"]
abbrev rankFunctor [HasFiniteProducts C] (k n : ℕ) : C ⥤ SimplicialObject C :=
  Functor.const SimplexCategoryᵒᵖ ⋙
    Functor.indexedProd.functor (C := C) (rankIndexFunctor k n)

/-- The degree-`n + 1` part of the `n`-coskeleton of the costandard simplicial power. -/
@[stacks 01GJ "costandard power matching functor"]
abbrev matchingFunctor (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] : C ⥤ C :=
  functor (C := C) k ⋙ SimplicialObject.cosk n ⋙
    (evaluation SimplexCategoryᵒᵖ C).obj (op ⦋n + 1⦌)

/-- The degree-`n + 1` component of the coskeleton unit for a costandard simplicial power. -/
@[stacks 01GJ "costandard power coskeleton unit"]
abbrev unitComponent (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] (T : C) :=
  ((coskAdj n).unit.app (object k T)).app (op ⦋n + 1⦌)

/-- At the first omitted degree, bounded image dimension is equivalent to
nonsurjectivity. -/
@[stacks 01GJ "bounded-rank top-degree criterion"]
theorem rank_top_iff (k n : ℕ) (alpha : Index k (n + 1)) :
    (image alpha).len ≤ n ↔ ¬Function.Surjective alpha.toOrderHom := sorry

/-- The bounded-rank indices in degree `n + 1` are canonically the boundary indices. -/
@[stacks 01GJ "bounded-rank top indices as boundary indices"]
def rankTopEquiv (k n : ℕ) :
    RankIndex k n ⦋n + 1⦌ ≃ BoundaryIndex k (n + 1) :=
  (Equiv.refl (Index k (n + 1))).subtypeEquiv (rank_top_iff k n)

/-- The top-degree bounded-rank equivalence retains the underlying simplex map. -/
@[simp, stacks 01GJ "bounded-rank top equivalence application"]
theorem rankTopEquiv_apply (k n : ℕ) (alpha : RankIndex k n ⦋n + 1⦌) :
    (rankTopEquiv k n alpha).1 = alpha.1 := sorry

namespace RankTruncationComparison

/-- The component of the canonical comparison from the bounded-rank power to the original
power in an `n`-truncated degree. -/
@[stacks 01GJ "bounded-rank truncation comparison component"]
def app [HasFiniteProducts C] (k n : ℕ) (T : C)
    (q : (SimplexCategory.Truncated n)ᵒᵖ) :
    ((truncation n).obj (rankObject k n T)).obj q ⟶
      ((truncation n).obj (object k T)).obj q :=
  Pi.lift (fun alpha : ⦋k⦌ ⟶ q.unop.obj ↦
    Pi.π (fun _ : RankIndex k n q.unop.obj ↦ T)
      (RankIndex.low q.unop alpha))

/-- The truncated comparison followed by a full-power projection is the bounded-rank
projection with the same underlying simplex map. -/
@[reassoc, stacks 01GJ "bounded-rank truncation comparison projection"]
theorem app_π [HasFiniteProducts C]
    (k n : ℕ) (T : C) (q : (SimplexCategory.Truncated n)ᵒᵖ)
    (alpha : ⦋k⦌ ⟶ q.unop.obj) :
    app k n T q ≫
        Pi.π (fun _ : ⦋k⦌ ⟶ q.unop.obj ↦ T) alpha =
      Pi.π (fun _ : RankIndex k n q.unop.obj ↦ T)
        (RankIndex.low q.unop alpha) := sorry

/-- The bounded-rank truncation comparison components are natural in the truncated simplex. -/
@[stacks 01GJ "bounded-rank truncation comparison naturality"]
theorem naturality [HasFiniteProducts C]
    (k n : ℕ) (T : C) {q r : (SimplexCategory.Truncated n)ᵒᵖ} (f : q ⟶ r) :
    ((truncation n).obj (rankObject k n T)).map f ≫
        app k n T r =
      app k n T q ≫
        ((truncation n).obj (object k T)).map f := sorry

end RankTruncationComparison

/-- Restricting the bounded-rank power through degree `n` maps canonically to the restriction
of the full costandard power. -/
@[stacks 01GJ "bounded-rank truncation comparison"]
def rankTruncationComparison [HasFiniteProducts C] (k n : ℕ) (T : C) :
    (truncation n).obj (rankObject k n T) ⟶
      (truncation n).obj (object k T) where
  app := RankTruncationComparison.app k n T
  naturality := fun _ _ f ↦ RankTruncationComparison.naturality k n T f

/-- The right-Kan universal property maps the explicit bounded-rank power to the chosen
coskeleton of the full costandard power. -/
@[stacks 01GJ "bounded-rank power to the chosen coskeleton"]
noncomputable def rankComparison (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] (T : C) :
    rankObject k n T ⟶ (cosk n).obj (object k T) :=
  ((cosk n).obj (object k T)).liftOfIsRightKanExtension
    ((coskAdj n).counit.app ((truncation n).obj (object k T)))
    (rankObject k n T) (rankTruncationComparison k n T)

/-- The right-Kan comparison recovers the bounded-rank truncation comparison after the
coskeleton counit. -/
@[reassoc, stacks 01GJ "bounded-rank right-Kan comparison factorization"]
theorem rankComparison_fac (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] (T : C)
    (q : SimplexCategory.Truncated n) :
    (rankComparison k n T).app (op q.obj) ≫
        ((coskAdj n).counit.app ((truncation n).obj (object k T))).app (op q) =
      (rankTruncationComparison k n T).app (op q) := sorry

/-- The coordinate of the matching object indexed by a bounded-rank simplex map, obtained
from its canonical image factorization. -/
@[stacks 01GJ "matching coordinate from the canonical image factorization"]
def matchingProjection (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] (T : C)
    (alpha : RankIndex k n ⦋n + 1⦌) :
    (matchingFunctor (C := C) k n).obj T ⟶ T :=
  ((cosk n).obj (object k T)).map (image.ι alpha.1).op ≫
    ((coskAdj n).counit.app ((truncation n).obj (object k T))).app
      (op alpha.imageObject) ≫
    Pi.π
      (fun _ : (coyoneda.obj (op ⦋k⦌)).obj (image alpha.1) ↦ T)
      (factorThruImage alpha.1)

namespace MatchingHom

/-- The explicit forward comparison from the chosen matching object to the boundary-indexed
power. -/
@[stacks 01GJ "matching object to boundary power component"]
def app (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] (T : C) :
    (matchingFunctor (C := C) k n).obj T ⟶
      (Pi.diagonal (C := C) (BoundaryIndex k (n + 1))).obj T :=
  Pi.lift (fun alpha : BoundaryIndex k (n + 1) ↦
    matchingProjection k n T ((rankTopEquiv k n).symm alpha))

/-- The forward matching comparison followed by a boundary-power projection is the canonical
image-factorization coordinate. -/
@[reassoc, stacks 01GJ "matching comparison boundary coordinate"]
theorem app_π (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] (T : C)
    (alpha : BoundaryIndex k (n + 1)) :
    app k n T ≫
        Pi.π (fun _ : BoundaryIndex k (n + 1) ↦ T) alpha =
      matchingProjection k n T ((rankTopEquiv k n).symm alpha) := sorry

/-- The forward matching comparison is natural in the repeated object. -/
@[stacks 01GJ "matching object to boundary power naturality"]
theorem naturality (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] {T T' : C} (f : T ⟶ T') :
    (matchingFunctor (C := C) k n).map f ≫ app k n T' =
      app k n T ≫
        (Pi.diagonal (C := C) (BoundaryIndex k (n + 1))).map f := sorry

end MatchingHom

/-- The explicit natural comparison from the chosen matching functor to the boundary power. -/
@[stacks 01GJ "matching object to boundary power"]
def matchingHom (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] :
    matchingFunctor (C := C) k n ⟶
      Pi.diagonal (C := C) (BoundaryIndex k (n + 1)) where
  app := MatchingHom.app k n
  naturality := fun _ _ f ↦ MatchingHom.naturality k n f

namespace MatchingInv

/-- The explicit inverse comparison first reindexes boundary factors by `rankTopEquiv`, then
uses the right-Kan comparison from the bounded-rank power. -/
@[stacks 01GJ "boundary power to matching object component"]
noncomputable def app (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] (T : C) :
    (Pi.diagonal (C := C) (BoundaryIndex k (n + 1))).obj T ⟶
      (matchingFunctor (C := C) k n).obj T :=
  (Pi.diagonal.reindex (C := C) (rankTopEquiv k n)).app T ≫
    (rankComparison k n T).app (op ⦋n + 1⦌)

/-- The inverse matching comparison is natural in the repeated object. -/
@[stacks 01GJ "boundary power to matching object naturality"]
theorem naturality (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] {T T' : C} (f : T ⟶ T') :
    (Pi.diagonal (C := C) (BoundaryIndex k (n + 1))).map f ≫
        app k n T' =
      app k n T ≫ (matchingFunctor (C := C) k n).map f := sorry

end MatchingInv

/-- The explicit natural comparison from the boundary power to the chosen matching functor. -/
@[stacks 01GJ "boundary power to matching object"]
noncomputable def matchingInv (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] :
    Pi.diagonal (C := C) (BoundaryIndex k (n + 1)) ⟶
      matchingFunctor (C := C) k n where
  app := MatchingInv.app k n
  naturality := fun _ _ f ↦ MatchingInv.naturality k n f

namespace MatchingIso

/-- The forward matching comparison followed by the explicit inverse is the identity. -/
@[stacks 01GJ "matching comparison forward-inverse law"]
theorem hom_inv (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] :
    matchingHom (C := C) k n ≫ matchingInv (C := C) k n =
      𝟙 (matchingFunctor (C := C) k n) := sorry

/-- The explicit inverse matching comparison followed by the forward map is the identity. -/
@[stacks 01GJ "matching comparison inverse-forward law"]
theorem inv_hom (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] :
    matchingInv (C := C) k n ≫ matchingHom (C := C) k n =
      𝟙 (Pi.diagonal (C := C) (BoundaryIndex k (n + 1))) := sorry

end MatchingIso

/-- The chosen coskeleton matching functor is canonically the power indexed by
nonsurjective simplex maps.  Both directions are explicit: the forward map uses canonical
image factorizations, and the inverse uses the bounded-rank right-Kan comparison. -/
@[stacks 01GJ "matching object as a boundary-indexed power"]
noncomputable def matchingIso (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] :
    matchingFunctor (C := C) k n ≅
      Pi.diagonal (C := C) (BoundaryIndex k (n + 1)) where
  hom := matchingHom k n
  inv := matchingInv k n
  hom_inv_id := MatchingIso.hom_inv k n
  inv_hom_id := MatchingIso.inv_hom k n

namespace MatchingIso

/-- The forward component of `matchingIso` is the explicit canonical-image comparison. -/
@[simp, stacks 01GJ "matching isomorphism forward component"]
theorem hom_app (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] (T : C) :
    (matchingIso (C := C) k n).hom.app T = MatchingHom.app k n T := sorry

/-- The inverse component of `matchingIso` is the bounded-rank right-Kan comparison. -/
@[simp, stacks 01GJ "matching isomorphism inverse component"]
theorem inv_app (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] (T : C) :
    (matchingIso (C := C) k n).inv.app T = MatchingInv.app k n T := sorry

/-- Under `matchingIso`, the degree-`n + 1` coskeleton unit is the product projection from all
costandard indices to the nonsurjective indices. -/
@[stacks 01GJ "coskeleton unit under the boundary matching isomorphism"]
theorem unit (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] (T : C) :
    unitComponent k n T ≫ (matchingIso (C := C) k n).hom.app T =
      (Pi.diagonal.reindex (C := C) (boundaryInclusion k (n + 1))).app T := sorry

end MatchingIso

/-- `IsProjection k n` is the proposition that the canonical matching isomorphism identifies
the degree-`n + 1` coskeleton unit with the boundary-index projection. -/
@[stacks 01GJ "canonical matching projection property"]
def IsProjection (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] : Prop :=
  ∀ T : C, unitComponent k n T ≫ (matchingIso (C := C) k n).hom.app T =
      (Pi.diagonal.reindex (C := C) (boundaryInclusion k (n + 1))).app T

/-- Equation 25.7.3.1 (Tag 01GJ): the degree-`n + 1` coskeleton unit of a costandard
simplicial power is functorially the projection onto the finite family of nonsurjective
simplex-map factors. -/
@[stacks 01GJ "finite projection description"]
theorem unit_isProjection (k n : ℕ) [HasFiniteProducts C]
    [Truncated.HasCoskeletons C n] :
    IsProjection (C := C) k n := sorry

end CategoryTheory.SimplicialObject.CostandardPower
