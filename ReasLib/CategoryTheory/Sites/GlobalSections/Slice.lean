module

public import ReasLib.CategoryTheory.Sites.GlobalSections.Terminal
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Hom
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Over

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe u v

namespace CategoryTheory.Sheaf

/-- A section over the terminal identity object of a slice site determines a global section. -/
theorem nonemptyGlobalSectionsOfSectionOnSliceTerminal
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify (J.over U) (Type (max u v))]
    [HasGlobalSectionsFunctor (J.over U) (Type (max u v))]
    (F : Sheaf (J.over U) (Type (max u v)))
    (x : F.obj.obj (op (Over.mk (𝟙 U)))) :
    Nonempty ((Sheaf.Γ (J.over U) (Type (max u v))).obj F) := by
  let α : (J.over U).uliftSheafifiedRepresentable (Over.mk (𝟙 U)) ⟶ F :=
    ((J.over U).uliftSheafifiedRepresentableHomEquiv F (Over.mk (𝟙 U))).symm x
  let τ : Sheaf.terminal (J.over U) Limits.Types.isTerminalPUnit ⟶ F :=
    (GrothendieckTopology.SheafifiedRepresentable.Over.mkIdIsoTerminal
      (J := J) U).inv ≫ α
  exact ⟨(Sheaf.ΓObjEquivTerminalHom (J.over U) F).symm τ⟩

end CategoryTheory.Sheaf
