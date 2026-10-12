/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.Cech.Nerve.Coefficients
public import ReasLib.CategoryTheory.Sites.Cohomology.Ext
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coefficient Cech complexes for sheaves

The represented degree-zero sections functor of an abelian sheaf supplies coefficients for the
generic arrow-level Cech construction.  The resulting complex is exposed in the site Cech
namespace; no chapter-specific construction or derived-choice data is needed downstream.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicTopology
open Opposite

noncomputable section

universe w v vA vB u uA uB

namespace CategoryTheory.Cech.Coefficients

variable {C : Type u} [Category.{v} C] [Limits.HasFiniteProducts C]
variable {A : Type uA} [Category.{vA} A] [Limits.HasProducts.{w} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Limits.HasProducts.{w} B] [Preadditive B]

/-- Postcomposition of coefficient presheaves by `F`. -/
abbrev pointwise (F : A ⥤ B) : (Cᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ B) :=
  (Functor.whiskeringRight Cᵒᵖ A B).obj F

/-- The canonical comparison between applying `F` to a product of coefficient values and taking
the product of their images. -/
noncomputable def productComponentIso (F : A ⥤ B)
    [∀ J : Type w, PreservesLimitsOfShape (Discrete J) F]
    (P : Cᵒᵖ ⥤ A) (X : (Limits.FormalCoproduct.{w} C)ᵒᵖ) :
    F.obj (((Limits.FormalCoproduct.evalOp.{w} C A).obj P).obj X) ≅
      ((Limits.FormalCoproduct.evalOp.{w} C B).obj (P ⋙ F)).obj X :=
  preservesLimitIso F
      (Discrete.functor (fun i : X.unop.I ↦ P.obj (op (X.unop.obj i)))) ≪≫
    Limits.lim.mapIso (Discrete.natIso (fun _ ↦ Iso.refl _))

variable (F : A ⥤ B) [F.Additive]
  [∀ J : Type w, PreservesLimitsOfShape (Discrete J) F]

/-- The Cech cosimplicial object after applying `F` degreewise. -/
abbrev cosimplicialSource (E : SimplicialObject (Limits.FormalCoproduct.{w} C)) :
    (Cᵒᵖ ⥤ A) ⥤ CosimplicialObject B :=
  Limits.FormalCoproduct.cosimplicialObjectFunctor E ⋙
    (CosimplicialObject.whiskering A B).obj F

/-- The Cech cosimplicial object formed after applying `F` pointwise to the coefficients. -/
abbrev cosimplicialTarget (E : SimplicialObject (Limits.FormalCoproduct.{w} C)) :
    (Cᵒᵖ ⥤ A) ⥤ CosimplicialObject B :=
  pointwise F ⋙ Limits.FormalCoproduct.cosimplicialObjectFunctor E

/-- The product comparison in one simplex of a coefficient Cech cosimplicial object. -/
noncomputable def cosimplicialComponentIso
    (E : SimplicialObject (Limits.FormalCoproduct.{w} C))
    (P : Cᵒᵖ ⥤ A) (n : SimplexCategory) :
    ((cosimplicialSource F E).obj P).obj n ≅
      ((cosimplicialTarget F E).obj P).obj n :=
  productComponentIso F P (E.rightOp.obj n)

/-- The simplexwise product comparisons commute with all cosimplicial structure maps. -/
theorem cosimplicialComponentIso_naturality
    (E : SimplicialObject (Limits.FormalCoproduct.{w} C))
    (P : Cᵒᵖ ⥤ A) {m n : SimplexCategory} (f : m ⟶ n) :
    ((cosimplicialSource F E).obj P).map f ≫
        (cosimplicialComponentIso F E P n).hom =
      (cosimplicialComponentIso F E P m).hom ≫
        ((cosimplicialTarget F E).obj P).map f := sorry

/-- The coefficient-product comparison on the Cech cosimplicial object of one presheaf. -/
noncomputable def cosimplicialAppIso
    (E : SimplicialObject (Limits.FormalCoproduct.{w} C))
    (P : Cᵒᵖ ⥤ A) :
    (cosimplicialSource F E).obj P ≅ (cosimplicialTarget F E).obj P :=
  NatIso.ofComponents (cosimplicialComponentIso F E P)
    (cosimplicialComponentIso_naturality F E P)

/-- The coefficient-product comparison is natural in the coefficient presheaf. -/
theorem cosimplicialAppIso_naturality
    (E : SimplicialObject (Limits.FormalCoproduct.{w} C))
    {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (cosimplicialSource F E).map f ≫ (cosimplicialAppIso F E Q).hom =
      (cosimplicialAppIso F E P).hom ≫ (cosimplicialTarget F E).map f := sorry

/-- Applying a product-preserving additive functor to coefficient values commutes canonically
with the Cech cosimplicial-object construction. -/
noncomputable def cosimplicialIso
    (E : SimplicialObject (Limits.FormalCoproduct.{w} C)) :
    cosimplicialSource F E ≅ cosimplicialTarget F E :=
  NatIso.ofComponents (cosimplicialAppIso F E)
    (cosimplicialAppIso_naturality F E)

/-- An additive functor commutes with passage from a cosimplicial object to its alternating
coface complex. -/
theorem map_alternatingCofaceMapComplex :
    AlgebraicTopology.alternatingCofaceMapComplex A ⋙
        F.mapHomologicalComplex (ComplexShape.up ℕ) =
      (CosimplicialObject.whiskering A B).obj F ⋙
        AlgebraicTopology.alternatingCofaceMapComplex B := sorry

/-- The coefficient Cech complex after applying `F` degreewise. -/
abbrev complexSource {I : Type w} (U : I → C) :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex B ℕ :=
  cechComplexFunctor U ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ)

/-- The Cech complex formed after applying `F` pointwise to the coefficients. -/
abbrev complexTarget {I : Type w} (U : I → C) :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex B ℕ :=
  pointwise F ⋙ cechComplexFunctor U

/-- Applying a product-preserving additive functor to coefficient values commutes canonically
with the Cech complex construction. -/
noncomputable def complexIso {I : Type w} (U : I → C) :
    complexSource F U ≅ complexTarget F U :=
  Functor.associator
      (Limits.FormalCoproduct.cosimplicialObjectFunctor
        (Limits.FormalCoproduct.mk I U).cech)
      (AlgebraicTopology.alternatingCofaceMapComplex A)
      (F.mapHomologicalComplex (ComplexShape.up ℕ)) ≪≫
    Functor.isoWhiskerLeft
      (Limits.FormalCoproduct.cosimplicialObjectFunctor
        (Limits.FormalCoproduct.mk I U).cech)
      (eqToIso (map_alternatingCofaceMapComplex F)) ≪≫
    (Functor.associator
      (Limits.FormalCoproduct.cosimplicialObjectFunctor
        (Limits.FormalCoproduct.mk I U).cech)
      ((CosimplicialObject.whiskering A B).obj F)
      (AlgebraicTopology.alternatingCofaceMapComplex B)).symm ≪≫
    Functor.isoWhiskerRight
      (cosimplicialIso F (Limits.FormalCoproduct.mk I U).cech)
      (AlgebraicTopology.alternatingCofaceMapComplex B) ≪≫
    Functor.associator (pointwise F)
      (Limits.FormalCoproduct.cosimplicialObjectFunctor
        (Limits.FormalCoproduct.mk I U).cech)
      (AlgebraicTopology.alternatingCofaceMapComplex B)

end CategoryTheory.Cech.Coefficients

namespace CategoryTheory.Sheaf.Cech

variable {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}

/-- The contravariant degree-zero sections functor represented by an abelian sheaf `F`. -/
@[stacks 07A1 "represented degree-zero sections functor"]
abbrev sectionsFunctor [HasWeakSheafify J AddCommGrpCat.{max u v}]
    (F : Sheaf J AddCommGrpCat.{max u v}) :
    (Sheaf J (Type (max u v)))ᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  (Sheaf.composeAndSheafify J AddCommGrpCat.free).op ⋙ preadditiveYoneda.obj F

section H0

variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v})]

/-- Represented degree-zero sections agree additively with degree-zero cohomology over a sheaf
of sets. -/
@[stacks 07A1 "represented sections as degree-zero cohomology"]
noncomputable def sectionsEquivH0
    (K : Sheaf J (Type (max u v))) (F : Sheaf J AddCommGrpCat.{max u v}) :
    (sectionsFunctor F).obj (op K) ≃+ cohomologyOverSheaf K F 0 :=
  (Abelian.Ext.addEquiv₀
    (C := Sheaf J AddCommGrpCat.{max u v})
    (X := (Sheaf.composeAndSheafify J AddCommGrpCat.free).obj K)
    (Y := F)).symm

/-- The `AddCommGrpCat` isomorphism underlying `sectionsEquivH0`. -/
@[stacks 07A1 "represented sections and degree-zero cohomology"]
noncomputable def sectionsIsoH0
    (K : Sheaf J (Type (max u v))) (F : Sheaf J AddCommGrpCat.{max u v}) :
    (sectionsFunctor F).obj (op K) ≅ cohomologyOverSheaf K F 0 :=
  (sectionsEquivH0 K F).toAddCommGrpIso

end H0

/-- The ordinary alternating Cech complex on represented degree-zero sections. -/
@[stacks 07A1 "represented degree-zero Cech complex"]
abbrev complex [HasWeakSheafify J AddCommGrpCat.{max u v}]
    {K K' : Sheaf J (Type (max u v))} (α : K' ⟶ K)
    (F : Sheaf J AddCommGrpCat.{max u v}) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  Arrow.Cech.complex (Arrow.mk α) (sectionsFunctor F)

/-- The extended alternating Cech complex on represented degree-zero sections. -/
@[stacks 07A1 "extended represented degree-zero Cech complex"]
noncomputable abbrev extended [HasWeakSheafify J AddCommGrpCat.{max u v}]
    {K K' : Sheaf J (Type (max u v))} (α : K' ⟶ K)
    (F : Sheaf J AddCommGrpCat.{max u v}) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  Arrow.Cech.extended (Arrow.mk α) (sectionsFunctor F)

end CategoryTheory.Sheaf.Cech
