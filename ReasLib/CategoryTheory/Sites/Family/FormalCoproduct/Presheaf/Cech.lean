/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Cech complexes of simplicial semi-representable families

This file owns the topology-independent Cech construction obtained by evaluating an additive
presheaf on every member of a simplicial semi-representable family and taking the alternating
coface complex.  It also provides the contravariant maps induced by simplicial morphisms.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily.Cech

open AlgebraicTopology Limits

variable {C : Type u} [Category.{v} C]

/-- Product evaluation on semi-representable families, functorially in an additive presheaf. -/
abbrev sectionsInCoefficients :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) ⥤
      ((Limits.FormalCoproduct.{w} C)ᵒᵖ ⥤ AddCommGrpCat.{max u v w}) :=
  FormalCoproduct.evalOp C AddCommGrpCat.{max u v w}

/-- Product evaluation on semi-representable families with fixed additive-presheaf
coefficients. -/
abbrev sections (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) :
    (Limits.FormalCoproduct.{w} C)ᵒᵖ ⥤ AddCommGrpCat.{max u v w} :=
  sectionsInCoefficients.obj F

/-- The alternating-coface complex of a simplicial semi-representable family, functorially in
the additive presheaf of coefficients. -/
abbrev complexInCoefficients
    (K : SimplicialObject (Limits.FormalCoproduct.{w} C)) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) ⥤
      CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  FormalCoproduct.cochainComplexFunctor K

/-- The alternating-coface complex of a simplicial semi-representable family with fixed
additive-presheaf coefficients. -/
abbrev complex (K : SimplicialObject (Limits.FormalCoproduct.{w} C))
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) :
    CochainComplex AddCommGrpCat.{max u v w} ℕ :=
  (complexInCoefficients K).obj F

/-- Cech cohomology of a simplicial semi-representable family, functorially in its
additive-presheaf coefficients. -/
abbrev cohomologyInCoefficients
    (K : SimplicialObject (Limits.FormalCoproduct.{w} C)) (p : ℕ) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) ⥤ AddCommGrpCat.{max u v w} :=
  complexInCoefficients K ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w}
      (ComplexShape.up ℕ) p

/-- Cech cohomology of a simplicial semi-representable family with fixed additive-presheaf
coefficients. -/
abbrev cohomology (K : SimplicialObject (Limits.FormalCoproduct.{w} C))
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (p : ℕ) :
    AddCommGrpCat.{max u v w} :=
  (cohomologyInCoefficients K p).obj F

/-- A simplicial morphism induces a contravariant map of semi-representable-family Cech
complexes. -/
noncomputable def complexMap
    {K L : SimplicialObject (Limits.FormalCoproduct.{w} C)} (f : K ⟶ L)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) :
    complex L F ⟶ complex K F :=
  (alternatingCofaceMapComplex AddCommGrpCat.{max u v w}).map
    (Functor.whiskerRight f.rightOp (sections F))

/-- The contravariant map on Cech cohomology induced by a simplicial morphism. -/
noncomputable def cohomologyMap
    {K L : SimplicialObject (Limits.FormalCoproduct.{w} C)} (f : K ⟶ L)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (p : ℕ) :
    cohomology L F p ⟶ cohomology K F p :=
  HomologicalComplex.homologyMap (complexMap f F) p

/-- The identity simplicial morphism induces the identity on Cech cohomology. -/
theorem cohomologyMap_id
    (K : SimplicialObject (Limits.FormalCoproduct.{w} C))
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (p : ℕ) :
    cohomologyMap (𝟙 K) F p = 𝟙 _ := sorry

/-- Contravariant Cech cohomology maps respect composition of simplicial morphisms. -/
theorem cohomologyMap_comp
    {K L M : SimplicialObject (Limits.FormalCoproduct.{w} C)}
    (f : K ⟶ L) (g : L ⟶ M)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (p : ℕ) :
    cohomologyMap (f ≫ g) F p =
      cohomologyMap g F p ≫ cohomologyMap f F p := sorry

/-- Simplicial refinement maps on Cech cohomology are natural in the additive-presheaf
coefficients. -/
theorem cohomologyMap_natural
    {K L : SimplicialObject (Limits.FormalCoproduct.{w} C)} (f : K ⟶ L)
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}} (φ : F ⟶ G) (p : ℕ) :
    (cohomologyInCoefficients L p).map φ ≫ cohomologyMap f G p =
      cohomologyMap f F p ≫ (cohomologyInCoefficients K p).map φ := sorry

end CategoryTheory.SemiRepresentableFamily.Cech
