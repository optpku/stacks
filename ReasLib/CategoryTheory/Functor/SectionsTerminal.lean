module

public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Sections of type-valued functors at initial and terminal objects

This leaf owns the initial-evaluation description of compatible sections of a type-valued functor
and its contravariant terminal-object specialization. Module-presheaf and sheaf APIs should build
on this result rather than reconstructing compatible families separately on each slice category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace CategoryTheory.Functor

variable {J : Type u} [Category.{v} J]

/-- Compatible sections of a type-valued functor are determined by their value at an initial
object. -/
noncomputable def sectionsEquivInitial
    (F : J ⥤ Type w) (I : J) (hI : IsInitial I) :
    F.sections ≃ F.obj I :=
  (Types.isLimitEquivSections (limitOfDiagramInitial hI F)).symm

/-- `sectionsEquivInitial` evaluates a compatible section at the chosen initial object. -/
@[simp]
theorem sectionsEquivInitial_apply
    (F : J ⥤ Type w) (I : J) (hI : IsInitial I) (s : F.sections) :
    sectionsEquivInitial F I hI s = s.1 I := sorry

/-- The inverse initial-evaluation equivalence reconstructs a section by transport from the
initial value. -/
@[simp]
theorem sectionsEquivInitial_symm_apply
    (F : J ⥤ Type w) (I : J) (hI : IsInitial I)
    (x : F.obj I) (X : J) :
    ((sectionsEquivInitial F I hI).symm x).1 X = F.map (hI.to X) x := sorry

/-- Initial evaluation is natural in a natural transformation of type-valued functors. -/
@[simp]
theorem sectionsEquivInitial_sectionsMap
    {F G : J ⥤ Type w} (I : J) (hI : IsInitial I)
    (η : F ⟶ G) (s : F.sections) :
    sectionsEquivInitial G I hI ((sectionsFunctor J).map η s) =
      η.app I (sectionsEquivInitial F I hI s) := sorry

/-- Reconstruction from an initial value is natural in a natural transformation of type-valued
functors. -/
@[simp]
theorem sectionsMap_sectionsEquivInitial_symm
    {F G : J ⥤ Type w} (I : J) (hI : IsInitial I)
    (η : F ⟶ G) (x : F.obj I) :
    (sectionsFunctor J).map η ((sectionsEquivInitial F I hI).symm x) =
      (sectionsEquivInitial G I hI).symm (η.app I x) := sorry

variable {C : Type u} [Category.{v} C]

/-- Compatible sections of a contravariant type-valued functor are determined by their value at a
terminal object. -/
noncomputable def sectionsEquivTerminal
    (F : Cᵒᵖ ⥤ Type w) (T : C) (hT : IsTerminal T) :
    F.sections ≃ F.obj (op T) :=
  sectionsEquivInitial F (op T) hT.op

/-- `sectionsEquivTerminal` evaluates a compatible section at the chosen terminal object. -/
@[simp]
theorem sectionsEquivTerminal_apply
    (F : Cᵒᵖ ⥤ Type w) (T : C) (hT : IsTerminal T) (s : F.sections) :
    sectionsEquivTerminal F T hT s = s.1 (op T) := sorry

/-- The inverse terminal-evaluation equivalence reconstructs a section by restriction from the
terminal value. -/
@[simp]
theorem sectionsEquivTerminal_symm_apply
    (F : Cᵒᵖ ⥤ Type w) (T : C) (hT : IsTerminal T)
    (x : F.obj (op T)) (X : C) :
    ((sectionsEquivTerminal F T hT).symm x).1 (op X) = F.map ((hT.from X).op) x := sorry

/-- Terminal evaluation is natural in a natural transformation of contravariant type-valued
functors. -/
@[simp]
theorem sectionsEquivTerminal_sectionsMap
    {F G : Cᵒᵖ ⥤ Type w} (T : C) (hT : IsTerminal T)
    (η : F ⟶ G) (s : F.sections) :
    sectionsEquivTerminal G T hT ((sectionsFunctor Cᵒᵖ).map η s) =
      η.app (op T) (sectionsEquivTerminal F T hT s) := sorry

/-- Reconstruction from a terminal value is natural in a natural transformation of contravariant
type-valued functors. -/
@[simp]
theorem sectionsMap_sectionsEquivTerminal_symm
    {F G : Cᵒᵖ ⥤ Type w} (T : C) (hT : IsTerminal T)
    (η : F ⟶ G) (x : F.obj (op T)) :
    (sectionsFunctor Cᵒᵖ).map η ((sectionsEquivTerminal F T hT).symm x) =
      (sectionsEquivTerminal G T hT).symm (η.app (op T) x) := sorry

section Over

variable {U : C}

/-- Sections of a contravariant type-valued functor on `C / U` are equivalent to its value at the
terminal object `U ⟶ U`. -/
noncomputable def overSectionsEquivEvaluation
    (F : (Over U)ᵒᵖ ⥤ Type w) :
    F.sections ≃ F.obj (op (Over.mk (𝟙 U))) :=
  sectionsEquivTerminal F (Over.mk (𝟙 U)) Over.mkIdTerminal

/-- `overSectionsEquivEvaluation` evaluates a slice section at `U ⟶ U`. -/
@[simp]
theorem overSectionsEquivEvaluation_apply
    (F : (Over U)ᵒᵖ ⥤ Type w) (s : F.sections) :
    overSectionsEquivEvaluation F s = s.1 (op (Over.mk (𝟙 U))) := sorry

/-- The inverse slice terminal-evaluation equivalence computes a reconstructed section at any
object of `C / U`. -/
@[simp]
theorem overSectionsEquivEvaluation_symm_apply
    (F : (Over U)ᵒᵖ ⥤ Type w)
    (x : F.obj (op (Over.mk (𝟙 U)))) (W : Over U) :
    ((overSectionsEquivEvaluation F).symm x).1 (op W) =
      F.map ((Over.mkIdTerminal.from W).op) x := sorry

/-- Slice terminal evaluation is natural in a natural transformation. -/
@[simp]
theorem overSectionsEquivEvaluation_sectionsMap
    {F G : (Over U)ᵒᵖ ⥤ Type w} (η : F ⟶ G) (s : F.sections) :
    overSectionsEquivEvaluation G ((sectionsFunctor (Over U)ᵒᵖ).map η s) =
      η.app (op (Over.mk (𝟙 U))) (overSectionsEquivEvaluation F s) := sorry

/-- Reconstruction from a slice terminal value is natural in a natural transformation. -/
@[simp]
theorem sectionsMap_overSectionsEquivEvaluation_symm
    {F G : (Over U)ᵒᵖ ⥤ Type w} (η : F ⟶ G)
    (x : F.obj (op (Over.mk (𝟙 U)))) :
    (sectionsFunctor (Over U)ᵒᵖ).map η ((overSectionsEquivEvaluation F).symm x) =
      (overSectionsEquivEvaluation G).symm (η.app (op (Over.mk (𝟙 U))) x) := sorry

end Over

end CategoryTheory.Functor
