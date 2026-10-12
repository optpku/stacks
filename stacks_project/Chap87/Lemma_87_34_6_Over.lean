/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap66.Lemma_66_18_3_Site
public import stacks_project.Chap87.Lemma_87_34_3_Reduction

/-!
# Étale morphisms of formal algebraic spaces over a base

The source category of Lemma 87.34.6 is the full subcategory of the étale
slice of functors of points over a formal algebraic space `X` on those
domains that are themselves formal algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}}

/-- The étale slice of functors of points over `X`: morphisms that are
representable by algebraic spaces and étale. -/
abbrev etaleComma (X : (Over S)ᵒᵖ ⥤ Type u) :=
  MorphismProperty.Over (@Etale S) ⊤ X

/-- `etaleComma X` is the étale slice `MorphismProperty.Over (@Etale S) ⊤ X`. -/
theorem etaleComma_def (X : (Over S)ᵒᵖ ⥤ Type u) :
    etaleComma X = MorphismProperty.Over (@Etale S) ⊤ X :=
  rfl

/-- The object property selecting étale slice objects whose domain is a formal
algebraic space. -/
def isFormalDomain (X : (Over S)ᵒᵖ ⥤ Type u) :
    ObjectProperty (etaleComma X) :=
  fun U ↦ IsFormalAlgebraicSpace U.left

/-- An object of the étale slice over `X` lies in `isFormalDomain X` if and only
if its domain is a formal algebraic space. -/
theorem isFormalDomain_iff {X : (Over S)ᵒᵖ ⥤ Type u} {U : etaleComma X} :
    isFormalDomain X U ↔ IsFormalAlgebraicSpace U.left :=
  Iff.rfl

/-- The category of morphisms `φ : U ⟶ X` of formal algebraic spaces that are
representable by algebraic spaces and étale. -/
abbrev EtaleOver (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X] :=
  (isFormalDomain X).FullSubcategory

/-- `EtaleOver X` is the full subcategory of `etaleComma X` on formal algebraic
space domains. -/
theorem EtaleOver_def (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X] :
    EtaleOver X = (isFormalDomain X).FullSubcategory :=
  rfl

/-- Construct an object of `EtaleOver X` from an étale morphism of formal
algebraic spaces into `X`. -/
def EtaleOver.mk {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace U] (φ : U ⟶ X)
    [Etale φ] : EtaleOver X where
  obj := MorphismProperty.Over.mk ⊤ φ inferInstance
  property := ‹IsFormalAlgebraicSpace U›

/-- The underlying functor of points of `EtaleOver.mk φ` is the domain of `φ`. -/
@[simp]
theorem EtaleOver.mk_left {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace U] (φ : U ⟶ X) [Etale φ] :
    (EtaleOver.mk φ).obj.left = U :=
  rfl

/-- The structural morphism of `EtaleOver.mk φ` is `φ`. -/
@[simp]
theorem EtaleOver.mk_hom {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace U] (φ : U ⟶ X) [Etale φ] :
    (EtaleOver.mk φ).obj.hom = φ :=
  rfl

/-- The identity morphism of `X` as an object of `EtaleOver X`. -/
def EtaleOver.self (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X] :
    EtaleOver X :=
  EtaleOver.mk (𝟙 X)

/-- The structural morphism of `EtaleOver.self X` is `𝟙 X`. -/
@[simp]
theorem EtaleOver.self_hom (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X] :
    (EtaleOver.self X).obj.hom = 𝟙 X :=
  rfl

/-- The structural morphism of an object of `EtaleOver X` is étale. -/
instance instEtale_etaleOver {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    (U : EtaleOver X) : Etale U.obj.hom :=
  U.obj.prop

/-- The domain of an object of `EtaleOver X` is a formal algebraic space. -/
instance instIsFormalAlgebraicSpace_etaleOver {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (U : EtaleOver X) :
    IsFormalAlgebraicSpace U.obj.left :=
  U.property

end AlgebraicGeometry.FormalAlgebraicSpace
