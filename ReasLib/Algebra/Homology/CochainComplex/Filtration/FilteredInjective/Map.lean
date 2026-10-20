/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.FullSubcategory
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Plus
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Functor.Naturality.Plus
public import ReasLib.CategoryTheory.Filtration.Complex.Finite.Bounded
public import ReasLib.CategoryTheory.Filtration.FiniteInjective.GradedPiece
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Mapping Bounded-Below Filtered-Injective Complexes

An additive functor preserving monomorphisms commutes with graded pieces on finite
filtered-injectives.  Here that objectwise comparison is lifted to a natural isomorphism of
cochain complexes.  The construction is independent of derived functors and spectral sequences.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.FilteredInjectivePlus.Map

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
  (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]

/-- View a bounded-below termwise filtered-injective complex as a bounded-below complex in the
full subcategory of finite filtered-injective objects. -/
@[stacks 05TW "filtered-injective full-subcategory bounded-below view"]
noncomputable abbrev plusSource :
    CochainComplex.FilteredInjectivePlus A ⥤
      CochainComplex.Plus (FilteredObject.Finite.FilteredInjective.category A) :=
  CochainComplex.Plus.TermsIn.toFullSubcategory
    (FilteredObject.Finite.FilteredInjective.property A)

/-- View a bounded-below termwise filtered-injective complex as an ordinary cochain complex in
the full subcategory of finite filtered-injective objects. -/
@[stacks 05TW "filtered-injective full-subcategory cochain view"]
noncomputable abbrev source :
    CochainComplex.FilteredInjectivePlus A ⥤
      CochainComplex (FilteredObject.Finite.FilteredInjective.category A) ℤ :=
  plusSource (A := A) ⋙
    CochainComplex.Plus.ι (FilteredObject.Finite.FilteredInjective.category A)

namespace GradedPiece

/-- The bounded-below functor obtained by mapping a filtered-injective complex termwise and then
taking its `p`-th graded piece. -/
@[stacks 05U0 "mapped graded-piece bounded-below functor on filtered-injectives"]
noncomputable abbrev plusMapped (p : ℤ) :
    CochainComplex.FilteredInjectivePlus A ⥤ CochainComplex.Plus B :=
  plusSource (A := A) ⋙
    (FilteredObject.Finite.FilteredInjective.GradedPiece.mappedFunctor F p).mapCochainComplexPlus

omit [F.PreservesMonomorphisms] in
/-- The bounded-below functor obtained by taking graded pieces of a filtered-injective complex
termwise and then applying `F`. -/
@[stacks 05U0 "termwise mapped graded-piece bounded-below functor on filtered-injectives"]
noncomputable abbrev plusTermwise (p : ℤ) :
    CochainComplex.FilteredInjectivePlus A ⥤ CochainComplex.Plus B :=
  plusSource (A := A) ⋙
    (FilteredObject.Finite.FilteredInjective.GradedPiece.termwiseFunctor F p).mapCochainComplexPlus

/-- Mapping and taking graded pieces commute naturally on bounded-below complexes of finite
filtered-injective objects. -/
@[stacks 05U0 "bounded-below mapped graded-piece comparison"]
noncomputable def plusIso (p : ℤ) : plusMapped F p ≅ plusTermwise F p :=
  Functor.isoWhiskerLeft (plusSource (A := A))
    (Functor.Cochain.Plus.natIso
      (FilteredObject.Finite.FilteredInjective.GradedPiece.natIso F p))

/-- Map a filtered-injective complex termwise and then take its `p`-th graded piece. -/
@[stacks 05U0 "mapped graded-piece cochain functor on filtered-injectives"]
noncomputable abbrev mapped (p : ℤ) :
    CochainComplex.FilteredInjectivePlus A ⥤ CochainComplex B ℤ :=
  source (A := A) ⋙
    (FilteredObject.Finite.FilteredInjective.GradedPiece.mappedFunctor F p).mapHomologicalComplex
      (up ℤ)

omit [F.PreservesMonomorphisms] in
/-- Take the `p`-th graded piece of a filtered-injective complex termwise and then apply `F`. -/
@[stacks 05U0 "termwise mapped graded-piece cochain functor on filtered-injectives"]
noncomputable abbrev termwise (p : ℤ) :
    CochainComplex.FilteredInjectivePlus A ⥤ CochainComplex B ℤ :=
  source (A := A) ⋙
    (FilteredObject.Finite.FilteredInjective.GradedPiece.termwiseFunctor F p).mapHomologicalComplex
      (up ℤ)

/-- The canonical natural isomorphism between graded pieces after termwise mapping and
termwise mapped graded pieces of bounded-below filtered-injective complexes. -/
@[stacks 05U0 "mapped graded-piece comparison for filtered-injective complexes"]
noncomputable def natIso (p : ℤ) : mapped F p ≅ termwise F p :=
  Functor.isoWhiskerLeft (source (A := A))
    (NatIso.mapHomologicalComplex
      (FilteredObject.Finite.FilteredInjective.GradedPiece.natIso F p) (up ℤ))

/-- The actual cochain complex obtained by mapping a bounded-below filtered-injective complex as
a finite filtered complex and then taking its `p`-th graded piece. -/
@[stacks 05U0 "mapped filtered-injective graded-piece complex"]
noncomputable abbrev mappedComplex (I : CochainComplex.FilteredInjectivePlus A) (p : ℤ) :
    CochainComplex B ℤ :=
  (((FilteredObject.Finite.CochainComplex.inclusion B).obj
    (((FilteredObject.Finite.mapFunctor F).mapHomologicalComplex (up ℤ)).obj
      ((CochainComplex.FilteredInjectivePlus.ι A).obj I))).gradedPiece p)

omit [F.PreservesMonomorphisms] in
/-- The cochain complex obtained by applying `F` to the canonical injective graded-piece view. -/
@[stacks 05U0 "termwise mapped filtered-injective graded-piece complex"]
noncomputable abbrev termwiseComplex
    (I : CochainComplex.FilteredInjectivePlus A) (p : ℤ) : CochainComplex B ℤ :=
  (F.mapCochainComplexPlus.obj
    ((FilteredObject.Finite.Plus.GradedPiece.cochain A p).obj I.obj)).obj

/-- The underlying complex of the bounded-below mapped comparison source is the actual graded
piece after mapping the finite filtered complex. -/
@[stacks 05U0 "mapped graded-piece bounded-below computation"]
theorem plusMapped_obj_obj
    (I : CochainComplex.FilteredInjectivePlus A) (p : ℤ) :
    ((plusMapped F p).obj I).obj = mappedComplex F I p := sorry

omit [F.PreservesMonomorphisms] in
/-- The underlying complex of the bounded-below mapped comparison target is obtained by applying
`F` to the canonical injective graded-piece view. -/
@[stacks 05U0 "termwise mapped graded-piece bounded-below computation"]
theorem plusTermwise_obj_obj
    (I : CochainComplex.FilteredInjectivePlus A) (p : ℤ) :
    ((plusTermwise F p).obj I).obj = termwiseComplex F I p := sorry

/-- The canonical cochain isomorphism from the graded piece after mapping a bounded-below
filtered-injective complex to the termwise image of its graded piece. -/
@[stacks 05U0 "mapped graded-piece comparison for filtered-injective complexes"]
noncomputable def cochainIso
    (I : CochainComplex.FilteredInjectivePlus A) (p : ℤ) :
    mappedComplex F I p ≅ termwiseComplex F I p :=
  (eqToIso (plusMapped_obj_obj F I p)).symm ≪≫
    (CochainComplex.Plus.ι B).mapIso ((plusIso F p).app I) ≪≫
      eqToIso (plusTermwise_obj_obj F I p)

/-- The map on actual mapped graded-piece complexes induced by a morphism of bounded-below
filtered-injective complexes. -/
@[stacks 05U0 "mapped filtered-injective graded-piece map"]
noncomputable abbrev mappedComplexMap
    {I J : CochainComplex.FilteredInjectivePlus A} (f : I ⟶ J) (p : ℤ) :
    mappedComplex F I p ⟶ mappedComplex F J p :=
  FilteredComplex.gradedPieceMap
    ((FilteredObject.Finite.CochainComplex.inclusion B).map
      (((FilteredObject.Finite.mapFunctor F).mapHomologicalComplex (up ℤ)).map
        ((CochainComplex.FilteredInjectivePlus.ι A).map f))) p

omit [F.PreservesMonomorphisms] in
/-- The termwise mapped graded-piece map induced by a morphism of bounded-below
filtered-injective complexes. -/
@[stacks 05U0 "termwise mapped filtered-injective graded-piece map"]
noncomputable abbrev termwiseComplexMap
    {I J : CochainComplex.FilteredInjectivePlus A} (f : I ⟶ J) (p : ℤ) :
    termwiseComplex F I p ⟶ termwiseComplex F J p :=
  (F.mapHomologicalComplex (up ℤ)).map
    (((FilteredObject.Finite.Plus.GradedPiece.cochain A p).map f.hom).hom)

/-- The canonical mapped graded-piece cochain isomorphism is natural in bounded-below
filtered-injective complexes. -/
@[reassoc, stacks 05U0 "naturality of the mapped graded-piece cochain comparison"]
theorem cochainIso_naturality
    {I J : CochainComplex.FilteredInjectivePlus A} (f : I ⟶ J) (p : ℤ) :
    mappedComplexMap F f p ≫ (cochainIso F J p).hom =
      (cochainIso F I p).hom ≫ termwiseComplexMap F f p := sorry

/-- The forward comparison in cochain degree `n` is the canonical objectwise graded-piece
comparison. -/
@[simp, stacks 05U0 "mapped graded-piece comparison for filtered-injective complexes"]
theorem natIso_hom_app_f (I : CochainComplex.FilteredInjectivePlus A) (p n : ℤ) :
    ((natIso F p).hom.app I).f n =
      FilteredObject.Finite.FilteredInjective.GradedPiece.comparison F
        ⟨I.obj.obj.X n, I.property n⟩ p := sorry

/-- The inverse comparison in cochain degree `n` is the inverse canonical objectwise
graded-piece comparison. -/
@[simp, stacks 05U0 "mapped graded-piece comparison for filtered-injective complexes"]
theorem natIso_inv_app_f (I : CochainComplex.FilteredInjectivePlus A) (p n : ℤ) :
    ((natIso F p).inv.app I).f n =
      (FilteredObject.Finite.FilteredInjective.GradedPiece.iso F
        ⟨I.obj.obj.X n, I.property n⟩ p).inv := sorry

end GradedPiece

end CochainComplex.FilteredInjectivePlus.Map
