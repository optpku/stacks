module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Limits.Presentation
public import Mathlib.CategoryTheory.Presentable.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Filtered colimits of finitely presented modules on QCQS algebraic spaces

Every quasi-coherent module on a quasi-compact and absolutely quasi-separated algebraic space
is a small filtered colimit of finitely presented modules.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Every quasi-coherent module on a quasi-compact and absolutely quasi-separated algebraic
space is a small filtered colimit of finitely presented module sheaves. -/
theorem isFinitePresentation_ind_of_qcqs {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (F : X.Modules) [F.IsQuasicoherent] :
    (SheafOfModules.isFinitePresentation (structureSheaf X)).ind.{u} F :=
  sorry

/-- A finite-type quasi-coherent module on a quasi-compact quasi-separated algebraic space
admits a small filtered colimit presentation by finitely presented modules with epimorphic
transition maps. -/
theorem exists_finitePresentation_colimitPresentation_epi
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I),
      ∃ pres : ColimitPresentation I F,
        (∀ i : I, (pres.diag.obj i).IsFinitePresentation) ∧
          ∀ {i i' : I} (f : i ⟶ i'), Epi (pres.diag.map f) :=
  sorry

/-- A finite-type quasi-coherent module on a quasi-compact quasi-separated algebraic space
admits an epimorphism from a finitely presented module. -/
theorem exists_finitePresentation_epi
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    ∃ (G : X.Modules) (_ : G.IsFinitePresentation) (f : G ⟶ F), Epi f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
