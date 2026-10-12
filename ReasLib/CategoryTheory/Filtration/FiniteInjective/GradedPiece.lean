/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Finite
public import ReasLib.CategoryTheory.Filtration.FiniteInjective.Injective
public import ReasLib.CategoryTheory.Filtration.GradedPiece.Comparison
public import ReasLib.CategoryTheory.Filtration.Map.Preadditive
public import ReasLib.CategoryTheory.Preadditive.Injective.Split
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Graded Pieces after Mapping Finite Filtered-Injectives

For a finite filtered-injective object, every successor inclusion is split because its source
stage is injective.  Consequently every additive functor preserves the corresponding cokernel.
This file packages the resulting comparison between mapping a filtration before taking a graded
piece and mapping the graded piece itself.  The comparison is exposed first on objects and then
as a natural isomorphism, independently of complexes or derived functors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective.GradedPiece

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
  (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]

/-- The canonical projection from the `p`-th stage of a mapped finite filtered-injective object
to the image under `F` of its original `p`-th graded piece. -/
@[stacks 05U0 "mapped graded-piece projection on finite filtered-injectives"]
noncomputable def projection (I : FilteredInjective.category A) (p : ℤ) :
    (FilteredObject.map F I.obj.obj).stage p ⟶ F.obj (I.obj.obj.gradedPiece p) :=
  (Subobject.underlyingIso (F.map (I.obj.obj.filtration.stage p).arrow)).hom ≫
    F.map (cokernel.π (I.obj.obj.succInclusion p))

/-- The mapped successor stage is killed by the canonical projection to the image of the
original graded piece. -/
@[stacks 05U0 "mapped graded-piece projection on finite filtered-injectives"]
theorem succInclusion_projection (I : FilteredInjective.category A) (p : ℤ) :
    (FilteredObject.map F I.obj.obj).succInclusion p ≫ projection F I p = 0 := sorry

/-- The canonical comparison from the graded piece of a mapped finite filtered-injective object
to the image under `F` of the original graded piece. -/
@[stacks 05U0 "graded-piece comparison on finite filtered-injectives"]
noncomputable def comparison (I : FilteredInjective.category A) (p : ℤ) :
    (FilteredObject.map F I.obj.obj).gradedPiece p ⟶ F.obj (I.obj.obj.gradedPiece p) :=
  FilteredObject.GradedPiece.desc (FilteredObject.map F I.obj.obj) p
    (projection F I p) (succInclusion_projection F I p)

/-- The graded-piece comparison for a finite filtered-injective object is an isomorphism. -/
@[stacks 05U0 "graded-piece comparison on finite filtered-injectives"]
theorem comparison_isIso (I : FilteredInjective.category A) (p : ℤ) :
    IsIso (comparison F I p) := sorry

/-- Mapping a finite filtered-injective object commutes canonically with taking its `p`-th
graded piece. -/
@[stacks 05U0 "graded-piece comparison on finite filtered-injectives"]
noncomputable def iso (I : FilteredInjective.category A) (p : ℤ) :
    (FilteredObject.map F I.obj.obj).gradedPiece p ≅ F.obj (I.obj.obj.gradedPiece p) :=
  @asIso _ _ _ _ (comparison F I p) (comparison_isIso F I p)

/-- The forward map of the canonical mapped graded-piece isomorphism is the cokernel
comparison. -/
@[simp, stacks 05U0 "graded-piece comparison on finite filtered-injectives"]
theorem iso_hom (I : FilteredInjective.category A) (p : ℤ) :
    (iso F I p).hom = comparison F I p := sorry

/-- The mapped graded-piece comparisons are natural in finite filtered-injective objects. -/
@[reassoc, stacks 05U0 "naturality of the graded-piece comparison on filtered-injectives"]
theorem comparison_naturality {I J : FilteredInjective.category A} (f : I ⟶ J) (p : ℤ) :
    (FilteredObject.Hom.map F f.hom.hom).gradedPieceMap p ≫ comparison F J p =
      comparison F I p ≫ F.map (f.hom.hom.gradedPieceMap p) := sorry

/-- The canonical mapped graded-piece isomorphisms are natural in finite
filtered-injective objects. -/
@[stacks 05U0 "naturality of the graded-piece isomorphism on filtered-injectives"]
theorem iso_naturality {I J : FilteredInjective.category A} (f : I ⟶ J) (p : ℤ) :
    (FilteredObject.Hom.map F f.hom.hom).gradedPieceMap p ≫ (iso F J p).hom =
      (iso F I p).hom ≫ F.map (f.hom.hom.gradedPieceMap p) := sorry

/-- The functor obtained by mapping a finite filtered-injective object and then taking its
`p`-th graded piece. -/
@[stacks 05U0 "mapped graded-piece functor on finite filtered-injectives"]
noncomputable abbrev mappedFunctor (p : ℤ) : FilteredInjective.category A ⥤ B :=
  FilteredInjective.inclusion A ⋙ FilteredObject.Finite.mapFunctor F ⋙
    FilteredObject.Finite.AssociatedGraded.functor B ⋙ GradedObject.eval p

/-- The `p`-th graded-piece functor on finite filtered-injective objects. -/
@[stacks 05U0 "graded-piece functor on finite filtered-injectives"]
noncomputable abbrev functor (p : ℤ) : FilteredInjective.category A ⥤ A :=
  FilteredInjective.inclusion A ⋙ FilteredObject.Finite.AssociatedGraded.functor A ⋙
    GradedObject.eval p

/-- The functor obtained by first taking a graded piece of a finite filtered-injective object
and then applying `F`. -/
@[stacks 05U0 "termwise mapped graded-piece functor on finite filtered-injectives"]
noncomputable abbrev termwiseFunctor (p : ℤ) : FilteredInjective.category A ⥤ B :=
  functor (A := A) p ⋙ F

/-- The canonical natural transformation from graded pieces after mapping to mapped graded
pieces on finite filtered-injective objects. -/
@[stacks 05U0 "natural graded-piece comparison on finite filtered-injectives"]
noncomputable def natTrans (p : ℤ) : mappedFunctor F p ⟶ termwiseFunctor F p where
  app I := comparison F I p
  naturality _ _ f := comparison_naturality F f p

/-- The canonical natural isomorphism identifying graded pieces after mapping finite
filtered-injectives with mapped graded pieces. -/
@[stacks 05U0 "natural graded-piece comparison on finite filtered-injectives"]
noncomputable def natIso (p : ℤ) : mappedFunctor F p ≅ termwiseFunctor F p :=
  NatIso.ofComponents (fun I ↦ iso F I p) (fun f ↦ iso_naturality F f p)

/-- The forward component of the natural mapped graded-piece isomorphism is the canonical
graded-piece comparison. -/
@[simp, stacks 05U0 "natural graded-piece comparison on finite filtered-injectives"]
theorem natIso_hom_app (I : FilteredInjective.category A) (p : ℤ) :
    (natIso F p).hom.app I = comparison F I p := sorry

/-- The inverse component of the natural mapped graded-piece isomorphism is the inverse of the
canonical graded-piece comparison. -/
@[simp, stacks 05U0 "natural graded-piece comparison on finite filtered-injectives"]
theorem natIso_inv_app (I : FilteredInjective.category A) (p : ℤ) :
    (natIso F p).inv.app I = (iso F I p).inv := sorry

end CategoryTheory.FilteredObject.Finite.FilteredInjective.GradedPiece
