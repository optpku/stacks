/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable

/-!
# Morphisms from sheafified representables

This module owns the universe-polymorphic Yoneda-style equivalence between
morphisms out of a sheafified representable and sections, together with its
functoriality in the target sheaf and representing object.
-/

@[expose] public section

open CategoryTheory Opposite

universe w u v

namespace CategoryTheory.GrothendieckTopology

noncomputable section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Morphisms from the sheafified representable of `U` to `F` are equivalent to sections of
`F` over `U`. -/
abbrev uliftSheafifiedRepresentableHomEquiv
    [HasWeakSheafify J (Type (max w u v))]
    (F : Sheaf J (Type (max w u v))) (U : C) :
    (J.uliftSheafifiedRepresentable U ⟶ F) ≃ F.obj.obj (op U) :=
  (((sheafificationAdjunction J (Type (max w u v))).homEquiv
    (CategoryTheory.uliftYoneda.{max w u v}.obj U) F).trans
      CategoryTheory.uliftYonedaEquiv.{max w u v})

/-- In the ambient universe, morphisms from the sheafified representable of `U` to `F` are
equivalent to sections of `F` over `U`. -/
abbrev sheafifiedRepresentableHomEquiv
    [HasWeakSheafify J (Type (max u v))]
    (F : Sheaf J (Type (max u v))) (U : C) :
    (J.sheafifiedRepresentable U ⟶ F) ≃ F.obj.obj (op U) :=
  J.uliftSheafifiedRepresentableHomEquiv F U

/-- The Hom/sections equivalence commutes with postcomposition by a sheaf morphism. -/
theorem uliftSheafifiedRepresentableHomEquiv_comp
    [HasWeakSheafify J (Type (max w u v))]
    {F G : Sheaf J (Type (max w u v))} {U : C}
    (alpha : J.uliftSheafifiedRepresentable U ⟶ F) (beta : F ⟶ G) :
    J.uliftSheafifiedRepresentableHomEquiv G U (alpha ≫ beta) =
      beta.hom.app (op U) (J.uliftSheafifiedRepresentableHomEquiv F U alpha) := sorry

/-- The ambient-universe Hom/sections equivalence commutes with postcomposition by a sheaf
morphism. -/
theorem sheafifiedRepresentableHomEquiv_comp
    [HasWeakSheafify J (Type (max u v))]
    {F G : Sheaf J (Type (max u v))} {U : C}
    (alpha : J.sheafifiedRepresentable U ⟶ F) (beta : F ⟶ G) :
    J.sheafifiedRepresentableHomEquiv G U (alpha ≫ beta) =
      beta.hom.app (op U) (J.sheafifiedRepresentableHomEquiv F U alpha) := sorry

/-- The Hom/sections equivalence commutes with restriction along a morphism of representing
objects. -/
theorem uliftSheafifiedRepresentableHomEquiv_naturality
    [HasWeakSheafify J (Type (max w u v))]
    {U V : C} (f : V ⟶ U) (F : Sheaf J (Type (max w u v)))
    (alpha : J.uliftSheafifiedRepresentable U ⟶ F) :
    J.uliftSheafifiedRepresentableHomEquiv F V
        (J.uliftSheafifiedRepresentableMap f ≫ alpha) =
      F.obj.map f.op (J.uliftSheafifiedRepresentableHomEquiv F U alpha) := sorry

/-- The ambient-universe Hom/sections equivalence commutes with restriction along a morphism of
representing objects. -/
theorem sheafifiedRepresentableHomEquiv_naturality
    [HasWeakSheafify J (Type (max u v))]
    {U V : C} (f : V ⟶ U) (F : Sheaf J (Type (max u v)))
    (alpha : J.sheafifiedRepresentable U ⟶ F) :
    J.sheafifiedRepresentableHomEquiv F V
        (J.sheafifiedRepresentableMap f ≫ alpha) =
      F.obj.map f.op (J.sheafifiedRepresentableHomEquiv F U alpha) := sorry

end

end CategoryTheory.GrothendieckTopology
