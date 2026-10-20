module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import ReasLib.CategoryTheory.Sites.GlobalSections.Terminal
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Terminal

/-!
# Global sections from a representable coequalizer

This leaf transports a coequalizer presentation of the terminal sheaf through
global sections.  The resulting equalizer statement is formulated entirely in
the canonical `ΓRes` API.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C]

/-- Global-section restriction equalizes the two restrictions induced by any
parallel pair `a b : V ⟶ U`. -/
theorem ΓRes_equalizes
    {A : Type w} [Category A] {J : GrothendieckTopology C}
    [HasWeakSheafify J A] [HasGlobalSectionsFunctor J A]
    {U V : C} (F : Sheaf J A) (a b : V ⟶ U) :
    F.ΓRes (op U) ≫ F.obj.map a.op = F.ΓRes (op U) ≫ F.obj.map b.op := sorry

/-- A terminal cofork presentation of sheafified representables identifies
global sections with compatible morphisms out of the represented parallel pair. -/
noncomputable def ΓObjEquivCompatibleHom
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type (max u v))]
    [HasGlobalSectionsFunctor J (Type (max u v))]
    {U V : C} (a b : V ⟶ U) (F : Sheaf J (Type (max u v)))
    (hcoeq : IsColimit
      (GrothendieckTopology.SheafifiedRepresentable.terminalCofork J a b)) :
    (Sheaf.Γ J (Type (max u v))).obj F ≃
      { q : J.sheafifiedRepresentable U ⟶ F //
        J.sheafifiedRepresentableMap a ≫ q =
          J.sheafifiedRepresentableMap b ≫ q } :=
  (ΓObjEquivTerminalHom J F).trans (Cofork.IsColimit.homIso hcoeq F)

/-- A compatible section over `U` comes from a unique global section whenever
the canonical terminal cofork is a coequalizer. -/
theorem existsUnique_globalSection_of_coequalizer
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type (max u v))]
    [HasGlobalSectionsFunctor J (Type (max u v))]
    {U V : C} (a b : V ⟶ U) (F : Sheaf J (Type (max u v)))
    (hcoeq : IsColimit
      (GrothendieckTopology.SheafifiedRepresentable.terminalCofork J a b))
    (y : F.obj.obj (op U)) (hy : F.obj.map a.op y = F.obj.map b.op y) :
    ∃! x : (Sheaf.Γ J (Type (max u v))).obj F, Sheaf.ΓRes F (op U) x = y := sorry

end CategoryTheory.Sheaf
