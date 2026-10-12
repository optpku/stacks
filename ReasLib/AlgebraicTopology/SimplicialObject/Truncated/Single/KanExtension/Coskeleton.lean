/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Single.Functor
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Pointwise
public import ReasLib.AlgebraicTopology.SimplexCategory.EpiMono
public import ReasLib.CategoryTheory.Functor.RightKanExtension.LimitMap

/-!
# Coskeleton of a truncated simplicial object concentrated in one degree

This leaf owns the pointwise coskeleton coordinates of `Truncated.concentrated B k`, their
structure-map formulas, and their natural assembly in the coefficient object.  It is independent
of biproduct decompositions and category-wide finite-limit instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open SimplexCategory
open scoped SimplexCategory.Truncated Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {A : Type u} [Category.{v} A]

namespace concentrated.coskeleton

variable [HasZeroObject A] [HasZeroMorphisms A]

namespace Internal

/-- The structured arrow represented by a monomorphism `[k] ⟶ [n]`. -/
abbrev topArrow {k n : ℕ} (f : MonoHom ⦋k⦌ ⦋n⦌) :
    StructuredArrow (op ⦋n⦌) (SimplexCategory.Truncated.inclusion k).op :=
  StructuredArrow.mk (Y := op (top k)) f.hom.op

/-- The pointwise limit diagram computing the degree-`n` coskeleton of `concentrated B k`. -/
abbrev diagram (B : A) (k n : ℕ) :
    StructuredArrow (op ⦋n⦌) (SimplexCategory.Truncated.inclusion k).op ⥤ A :=
  StructuredArrow.proj (op ⦋n⦌) (SimplexCategory.Truncated.inclusion k).op ⋙
    concentrated B k

end Internal

/-- The canonical projection from degree `n` of the coskeleton of `concentrated B k` to the
factor indexed by `f : MonoHom ⦋k⦌ ⦋n⦌`. -/
@[stacks 0190 "coskeleton factor projection"]
noncomputable def π (B : A) {k n : ℕ}
    [(concentrated B k).HasPointwiseCoskeleton] (f : MonoHom ⦋k⦌ ⦋n⦌) :
    (concentrated B k).coskeleton.obj (op ⦋n⦌) ⟶ B :=
  (Functor.RightKanExtension.objIsoLimit
      (SimplexCategory.Truncated.inclusion k).op
      (concentrated B k) (op ⦋n⦌)).hom ≫
    limit.π (Internal.diagram B k n) (Internal.topArrow f) ≫ topInv B k

/-- The coskeleton projection is the corresponding simplicial operator followed by the
top-degree counit leg. -/
@[stacks 0190 "coskeleton projection through the counit"]
theorem π.eq_map_counit (B : A) {k n : ℕ}
    [(concentrated B k).HasPointwiseCoskeleton] (f : MonoHom ⦋k⦌ ⦋n⦌) :
    π B f =
      (concentrated B k).coskeleton.map f.hom.op ≫
        ((SimplexCategory.Truncated.inclusion k).op.rightKanExtensionCounit
          (concentrated B k)).app (op (top k)) ≫
        topInv B k := sorry

/-- A coskeleton structure map sends a projection to the partially postcomposed monic factor,
or to zero when the composite is not monic. -/
@[stacks 0190 "coskeleton structure map on a projection"]
theorem map_π (B : A) {k n n' : ℕ}
    [(concentrated B k).HasPointwiseCoskeleton]
    (f : ⦋n⦌ ⟶ ⦋n'⦌) (b : MonoHom ⦋k⦌ ⦋n⦌) :
    (concentrated B k).coskeleton.map f.op ≫ π B b =
      (b.postcomp f).elim 0 (fun c ↦ π B c) := sorry

/-- A coskeleton structure map sends a monic composite to its corresponding projection. -/
@[stacks 0190 "coskeleton structure map on a monic composite"]
theorem map_π_of_mono (B : A) {k n n' : ℕ}
    [(concentrated B k).HasPointwiseCoskeleton]
    (f : ⦋n⦌ ⟶ ⦋n'⦌) (b : MonoHom ⦋k⦌ ⦋n⦌)
    [Mono (b.hom ≫ f)] :
    (concentrated B k).coskeleton.map f.op ≫ π B b =
      π B ⟨b.hom ≫ f, inferInstance⟩ := sorry

/-- Explicit-proof bridge for the coskeleton structure map on a monic composite. -/
@[stacks 0190 "coskeleton structure map with an explicit monomorphism proof"]
theorem map_π_of_mono.explicit (B : A) {k n n' : ℕ}
    [(concentrated B k).HasPointwiseCoskeleton]
    (f : ⦋n⦌ ⟶ ⦋n'⦌) (b : MonoHom ⦋k⦌ ⦋n⦌)
    (h : Mono (b.hom ≫ f)) :
    (concentrated B k).coskeleton.map f.op ≫ π B b =
      π B ⟨b.hom ≫ f, h⟩ := sorry

/-- A coskeleton structure map followed by a factor projection vanishes when the corresponding
composite is not monic. -/
@[stacks 0190 "coskeleton structure map on a nonmonic composite"]
theorem map_π_of_not_mono (B : A) {k n n' : ℕ}
    [(concentrated B k).HasPointwiseCoskeleton]
    (f : ⦋n⦌ ⟶ ⦋n'⦌) (b : MonoHom ⦋k⦌ ⦋n⦌)
    (h : ¬ Mono (b.hom ≫ f)) :
    (concentrated B k).coskeleton.map f.op ≫ π B b = 0 := sorry

namespace degree

/-- For fixed `k` and `n`, evaluate the coskeleton of the concentrated object in simplicial
degree `n`, functorially in the coefficient object. -/
@[stacks 0190 "degreewise concentrated coskeleton functor"]
noncomputable abbrev functor (k n : ℕ)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k] : A ⥤ A :=
  concentrated.functor (A := A) k ⋙ SimplicialObject.Truncated.cosk k ⋙
    (evaluation SimplexCategoryᵒᵖ A).obj (op ⦋n⦌)

/-- The degreewise concentrated-coskeleton functor has the expected object value. -/
@[simp, stacks 0190 "degreewise concentrated coskeleton object formula"]
theorem functor_obj (k n : ℕ)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k] (B : A) :
    (functor (A := A) k n).obj B =
      ((SimplicialObject.Truncated.cosk k).obj (concentrated B k)).obj (op ⦋n⦌) := sorry

/-- The degreewise concentrated-coskeleton functor evaluates coefficient morphisms in degree
`n`. -/
@[simp, stacks 0190 "degreewise concentrated coskeleton map formula"]
theorem functor_map (k n : ℕ)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k]
    {B D : A} (f : B ⟶ D) :
    (functor (A := A) k n).map f =
      ((SimplicialObject.Truncated.cosk k).map (concentrated.map k f)).app (op ⦋n⦌) := sorry

/-- A coefficient morphism commutes with the canonical coskeleton factor map. -/
@[stacks 0190 "concentrated coskeleton factor naturality"]
theorem π_naturality {k n : ℕ}
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k]
    (b : MonoHom ⦋k⦌ ⦋n⦌) {B D : A} (f : B ⟶ D) :
    (functor (A := A) k n).map f ≫ coskeleton.π D b =
      coskeleton.π B b ≫ f := sorry

/-- The canonical coskeleton factor map, natural in the coefficient object. -/
@[stacks 0190 "natural concentrated coskeleton factor map"]
noncomputable def π {k n : ℕ}
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k]
    (b : MonoHom ⦋k⦌ ⦋n⦌) : functor (A := A) k n ⟶ 𝟭 A where
  app B := coskeleton.π B b
  naturality _ _ f := π_naturality b f

/-- A component of the natural coskeleton factor map is the corresponding objectwise map. -/
@[simp, stacks 0190 "natural concentrated coskeleton factor component"]
theorem π_app {k n : ℕ}
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k]
    (b : MonoHom ⦋k⦌ ⦋n⦌) (B : A) :
    (π (A := A) b).app B = coskeleton.π B b := sorry

end degree

end concentrated.coskeleton

end CategoryTheory.SimplicialObject.Truncated
