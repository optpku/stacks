/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Yoneda

/-!
# Sheafified representable presheaves

The sheafified Yoneda embedding `J.sheafifiedRepresentable U` sends an object `U`
to the sheafification of the representable presheaf `h_U`. This is the fundamental
construction underlying representability in algebraic geometry.

## Main definitions

- `GrothendieckTopology.sheafifiedRepresentable` — sheafification of h_U
- `GrothendieckTopology.sheafifiedRepresentableFunctor` — the functor C ⥤ Sheaf J
- `GrothendieckTopology.sheafifiedRepresentableMap` — functorial maps
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w v u

noncomputable section

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The universe-lifted sheafified representable: sheafification of `uliftYoneda.obj U`. -/
abbrev uliftSheafifiedRepresentable [HasWeakSheafify J (Type (max w u v))] (U : C) :
    Sheaf J (Type (max w u v)) :=
  (presheafToSheaf J (Type (max w u v))).obj (uliftYoneda.{max w u v}.obj U)

/-- The sheafified representable presheaf at `U`. -/
abbrev sheafifiedRepresentable [HasWeakSheafify J (Type (max u v))] (U : C) :
    Sheaf J (Type (max u v)) :=
  J.uliftSheafifiedRepresentable U

namespace SheafifiedRepresentable

/-- Textbook-style notation for the sheafified representable at `U`. -/
scoped notation:max "h[" U "]^#[" J "]" =>
  CategoryTheory.GrothendieckTopology.sheafifiedRepresentable J U

end SheafifiedRepresentable

/-- The universe-lifted sheafified Yoneda functor `C ⥤ Sheaf J (Type _)`. -/
abbrev uliftSheafifiedRepresentableFunctor [HasWeakSheafify J (Type (max w u v))] :
    C ⥤ Sheaf J (Type (max w u v)) :=
  uliftYoneda.{max w u v} ⋙ presheafToSheaf J (Type (max w u v))

/-- The universe-lifted functorial map between sheafified representables. -/
abbrev uliftSheafifiedRepresentableMap [HasWeakSheafify J (Type (max w u v))]
    {U V : C} (f : V ⟶ U) :
    J.uliftSheafifiedRepresentable V ⟶ J.uliftSheafifiedRepresentable U :=
  J.uliftSheafifiedRepresentableFunctor.map f

/-- The sheafified Yoneda functor `C ⥤ Sheaf J (Type _)` in the ambient universe. -/
abbrev sheafifiedRepresentableFunctor [HasWeakSheafify J (Type (max u v))] :
    C ⥤ Sheaf J (Type (max u v)) :=
  uliftYoneda.{max u v} ⋙ presheafToSheaf J (Type (max u v))

/-- The functorial map between sheafified representables. -/
abbrev sheafifiedRepresentableMap [HasWeakSheafify J (Type (max u v))]
    {U V : C} (f : V ⟶ U) :
    J.sheafifiedRepresentable V ⟶ J.sheafifiedRepresentable U :=
  J.sheafifiedRepresentableFunctor.map f

/-- A sheafified representable map is locally surjective (the sheafification unit
covers it). -/
theorem isLocallySurjective_sheafifiedRepresentableMap
    [HasWeakSheafify J (Type (max u v))] {U V : C} (f : V ⟶ U)
    (hf : Sieve.generate (Presieve.ofArrows (fun _ : Unit ↦ V) (fun _ ↦ f)) ∈ J U) :
    Sheaf.IsLocallySurjective (J.sheafifiedRepresentableMap f) := sorry

end CategoryTheory.GrothendieckTopology
