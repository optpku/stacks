/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Category
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.CategoryTheory.InverseSystem.Sequential

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The inverse system of `A`-modules obtained by taking global sections of a coherent
formal module on the open subscheme in an affine algebraization setup. -/
abbrev sectionsSystem (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) :
    SequentialInverseSystem (ModuleCat A) :=
  F.obj ⋙ (SheafOfModules.isCoherent (S.U.toScheme).ringCatSheaf).ι ⋙
    Scheme.Hom.globalSectionsFunctor S.U.ι

/-- Stage `n` of `sectionsSystem S F` is the global-sections module of the `n`th
coherent formal-module stage, with scalars induced by `S.U.ι`. -/
theorem sectionsSystem_obj (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (n : ℕ) :
    (sectionsSystem S F).obj (op n) =
      (Scheme.Hom.globalSectionsFunctor S.U.ι).obj
        ((SheafOfModules.isCoherent (S.U.toScheme).ringCatSheaf).ι.obj
          (F.obj.obj (op n))) := sorry

/-- The module of global sections obtained as the categorical inverse limit of a
coherent formal-module system on an affine algebraization open subscheme. -/
noncomputable def sectionsLimit (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) : ModuleCat A :=
  limit (sectionsSystem S F)

end AlgebraicGeometry.Scheme.CoherentFormalModules
