/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleOver
public import stacks_project.Chap66.Lemma_66_18_3_Site
public import stacks_project.Chap87.Lemma_87_34_3_Reduction

/-! # Étale morphisms of formal algebraic spaces over a base

The formal étale slice and its constructors are owned by the shared library.
The legacy reduction interface remains available to the chapter's consumers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}}

#check (AlgebraicGeometry.FormalAlgebraicSpace.etaleComma :
    ∀ (X : (Over S)ᵒᵖ ⥤ Type u), Type (u + 1))

#check (AlgebraicGeometry.FormalAlgebraicSpace.etaleComma_def :
    ∀ (X : (Over S)ᵒᵖ ⥤ Type u),
    etaleComma X = MorphismProperty.Over (@Etale S) ⊤ X)

#check (AlgebraicGeometry.FormalAlgebraicSpace.isFormalDomain :
    ∀ (X : (Over S)ᵒᵖ ⥤ Type u),
    ObjectProperty (etaleComma X))

#check (AlgebraicGeometry.FormalAlgebraicSpace.isFormalDomain_iff :
    ∀ {X : (Over S)ᵒᵖ ⥤ Type u} {U : etaleComma X},
    isFormalDomain X U ↔ IsFormalAlgebraicSpace U.left)

#check (AlgebraicGeometry.FormalAlgebraicSpace.EtaleOver :
    ∀ (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X], Type (u + 1))

#check (AlgebraicGeometry.FormalAlgebraicSpace.EtaleOver_def :
    ∀ (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X],
    EtaleOver X = (isFormalDomain X).FullSubcategory)

#check (AlgebraicGeometry.FormalAlgebraicSpace.EtaleOver.mk :
    ∀ {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace U] (φ : U ⟶ X)
    [Etale φ],
    EtaleOver X)

#check (AlgebraicGeometry.FormalAlgebraicSpace.EtaleOver.mk_left :
    ∀ {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace U] (φ : U ⟶ X) [Etale φ],
    (EtaleOver.mk φ).obj.left = U)

#check (AlgebraicGeometry.FormalAlgebraicSpace.EtaleOver.mk_hom :
    ∀ {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    {U : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace U] (φ : U ⟶ X) [Etale φ],
    (EtaleOver.mk φ).obj.hom = φ)

#check (AlgebraicGeometry.FormalAlgebraicSpace.EtaleOver.self :
    ∀ (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X],
    EtaleOver X)

#check (AlgebraicGeometry.FormalAlgebraicSpace.EtaleOver.self_hom :
    ∀ (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X],
    (EtaleOver.self X).obj.hom = 𝟙 X)

#check (AlgebraicGeometry.FormalAlgebraicSpace.instEtale_etaleOver :
    ∀ {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    (U : EtaleOver X),
    Etale U.obj.hom)

#check (AlgebraicGeometry.FormalAlgebraicSpace.instIsFormalAlgebraicSpace_etaleOver :
    ∀ {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (U : EtaleOver X),
    IsFormalAlgebraicSpace U.obj.left)

end AlgebraicGeometry.FormalAlgebraicSpace
