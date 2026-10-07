module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Single.Functor
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Pointwise
public import ReasLib.AlgebraicTopology.SimplexCategory.EpiMono
public import ReasLib.CategoryTheory.Functor.LeftKanExtension.ColimitMap

/-!
# Skeleton of a truncated simplicial object concentrated in one degree

This leaf owns the pointwise skeleton coordinates of `Truncated.concentrated B k`, their
structure-map formulas, and their natural assembly in the coefficient object.  It is independent
of biproduct decompositions and category-wide finite-colimit instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open SimplexCategory
open scoped SimplexCategory.Truncated Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {A : Type u} [Category.{v} A]

namespace concentrated.skeleton

variable [HasZeroObject A] [HasZeroMorphisms A]

namespace Internal

/-- The costructured arrow represented by an epimorphism `[n] ⟶ [k]`. -/
abbrev topArrow {k n : ℕ} (f : EpiHom ⦋n⦌ ⦋k⦌) :
    CostructuredArrow (SimplexCategory.Truncated.inclusion k).op (op ⦋n⦌) :=
  CostructuredArrow.mk (Y := op (top k)) f.hom.op

/-- The pointwise colimit diagram computing the degree-`n` skeleton of `concentrated B k`. -/
abbrev diagram (B : A) (k n : ℕ) :
    CostructuredArrow (SimplexCategory.Truncated.inclusion k).op (op ⦋n⦌) ⥤ A :=
  CostructuredArrow.proj (SimplexCategory.Truncated.inclusion k).op (op ⦋n⦌) ⋙
    concentrated B k

end Internal

/-- The canonical map from the summand indexed by `f : EpiHom ⦋n⦌ ⦋k⦌` into degree `n` of
the skeleton of `concentrated B k`. -/
@[stacks 0190 "skeleton summand inclusion"]
noncomputable def ι (B : A) {k n : ℕ}
    [(concentrated B k).HasPointwiseSkeleton] (f : EpiHom ⦋n⦌ ⦋k⦌) :
    B ⟶ (concentrated B k).skeleton.obj (op ⦋n⦌) :=
  topHom B k ≫ colimit.ι (Internal.diagram B k n) (Internal.topArrow f) ≫
    ((SimplexCategory.Truncated.inclusion k).op.leftKanExtensionObjIsoColimit
      (concentrated B k) (op ⦋n⦌)).inv

/-- The skeleton summand map is the top-degree unit leg followed by the corresponding
simplicial operator. -/
@[stacks 0190 "skeleton summand map through the unit"]
theorem ι.eq_unit_map (B : A) {k n : ℕ}
    [(concentrated B k).HasPointwiseSkeleton] (f : EpiHom ⦋n⦌ ⦋k⦌) :
    ι B f =
      topHom B k ≫
        ((SimplexCategory.Truncated.inclusion k).op.leftKanExtensionUnit
          (concentrated B k)).app (op (top k)) ≫
        (concentrated B k).skeleton.map f.hom.op := sorry

/-- A skeleton structure map sends a summand to the partially precomposed epic summand, or to
zero when the composite is not epic. -/
@[stacks 0190 "skeleton structure map on a summand"]
theorem map_ι (B : A) {k n n' : ℕ}
    [(concentrated B k).HasPointwiseSkeleton]
    (f : ⦋n⦌ ⟶ ⦋n'⦌) (a : EpiHom ⦋n'⦌ ⦋k⦌) :
    ι B a ≫ (concentrated B k).skeleton.map f.op =
      (a.precomp f).elim 0 (fun c ↦ ι B c) := sorry

/-- A skeleton structure map sends an epic composite to its corresponding summand. -/
@[stacks 0190 "skeleton structure map on an epic composite"]
theorem map_ι_of_epi (B : A) {k n n' : ℕ}
    [(concentrated B k).HasPointwiseSkeleton]
    (f : ⦋n⦌ ⟶ ⦋n'⦌) (a : EpiHom ⦋n'⦌ ⦋k⦌)
    [Epi (f ≫ a.hom)] :
    ι B a ≫ (concentrated B k).skeleton.map f.op =
      ι B ⟨f ≫ a.hom, inferInstance⟩ := sorry

/-- Explicit-proof bridge for the skeleton structure map on an epic composite. -/
@[stacks 0190 "skeleton structure map with an explicit epimorphism proof"]
theorem map_ι_of_epi.explicit (B : A) {k n n' : ℕ}
    [(concentrated B k).HasPointwiseSkeleton]
    (f : ⦋n⦌ ⟶ ⦋n'⦌) (a : EpiHom ⦋n'⦌ ⦋k⦌)
    (h : Epi (f ≫ a.hom)) :
    ι B a ≫ (concentrated B k).skeleton.map f.op =
      ι B ⟨f ≫ a.hom, h⟩ := sorry

/-- A skeleton structure map vanishes on a summand when the corresponding composite is not
epic. -/
@[stacks 0190 "skeleton structure map on a nonepic composite"]
theorem map_ι_of_not_epi (B : A) {k n n' : ℕ}
    [(concentrated B k).HasPointwiseSkeleton]
    (f : ⦋n⦌ ⟶ ⦋n'⦌) (a : EpiHom ⦋n'⦌ ⦋k⦌)
    (h : ¬ Epi (f ≫ a.hom)) :
    ι B a ≫ (concentrated B k).skeleton.map f.op = 0 := sorry

namespace degree

/-- For fixed `k` and `n`, evaluate the skeleton of the concentrated object in simplicial
degree `n`, functorially in the coefficient object. -/
@[stacks 0190 "degreewise concentrated skeleton functor"]
noncomputable abbrev functor (k n : ℕ)
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k] : A ⥤ A :=
  concentrated.functor (A := A) k ⋙ SimplicialObject.Truncated.sk k ⋙
    (evaluation SimplexCategoryᵒᵖ A).obj (op ⦋n⦌)

/-- The degreewise concentrated-skeleton functor has the expected object value. -/
@[simp, stacks 0190 "degreewise concentrated skeleton object formula"]
theorem functor_obj (k n : ℕ)
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k] (B : A) :
    (functor (A := A) k n).obj B =
      ((SimplicialObject.Truncated.sk k).obj (concentrated B k)).obj (op ⦋n⦌) := sorry

/-- The degreewise concentrated-skeleton functor evaluates coefficient morphisms in degree
`n`. -/
@[simp, stacks 0190 "degreewise concentrated skeleton map formula"]
theorem functor_map (k n : ℕ)
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    {B D : A} (f : B ⟶ D) :
    (functor (A := A) k n).map f =
      ((SimplicialObject.Truncated.sk k).map (concentrated.map k f)).app (op ⦋n⦌) := sorry

/-- A coefficient morphism commutes with the canonical skeleton summand map. -/
@[stacks 0190 "concentrated skeleton summand naturality"]
theorem ι_naturality {k n : ℕ}
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    (a : EpiHom ⦋n⦌ ⦋k⦌) {B D : A} (f : B ⟶ D) :
    f ≫ skeleton.ι D a =
      skeleton.ι B a ≫ (functor (A := A) k n).map f := sorry

/-- The canonical skeleton summand map, natural in the coefficient object. -/
@[stacks 0190 "natural concentrated skeleton summand map"]
noncomputable def ι {k n : ℕ}
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    (a : EpiHom ⦋n⦌ ⦋k⦌) : 𝟭 A ⟶ functor (A := A) k n where
  app B := skeleton.ι B a
  naturality _ _ f := ι_naturality a f

/-- A component of the natural skeleton summand map is the corresponding objectwise map. -/
@[simp, stacks 0190 "natural concentrated skeleton summand component"]
theorem ι_app {k n : ℕ}
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    (a : EpiHom ⦋n⦌ ⦋k⦌) (B : A) :
    (ι (A := A) a).app B = skeleton.ι B a := sorry

end degree

end concentrated.skeleton

end CategoryTheory.SimplicialObject.Truncated
