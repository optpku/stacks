module
public import stacks_project.Chap60.Remark_60_24_11_Comparison_DeRham
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.DegreeZero
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.DegreeOne
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationMonoidal

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
universe u
namespace CrystallineSheafDegreeBridges

variable {A : Type u} [CommRing A] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
variable (M : Y.Modules)

/-- Restriction of scalars as an actual functor on all local sections. -/
noncomputable def baseFunctor : Y.Modules ⥤ TopCat.Sheaf (ModuleCat.{u} A) Y.toTopCat :=
  SheafOfModules.forgetToSheafModuleCat Y.ringCatSheaf (op ⊤)
      (initialOpOfTerminal isTerminalTop) ⋙
    sheafCompose (Opens.grothendieckTopology Y.toTopCat)
      (ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap f))

/-- Tensoring a genuine sheaf with the structure module is canonically
the sheaf itself, using the actual sheafification tensor comparison. -/
noncomputable def tensorStructureIso : moduleTensor (𝒪 := Y.sheaf) M (unitModule _ Y.sheaf) ≅ M :=
  ModuleSheafification.tensorObjIso Y.sheaf M (unitModule _ Y.sheaf) ≪≫
    (moduleSheafification Y.sheaf).mapIso (ρ_ M.val) ≪≫
      moduleSheafificationValIso Y.sheaf M

/-- The zero-degree sheaf term is canonically the original coefficient
sheaf; both arrows are fixed by exterior degree zero and tensor-unit maps. -/
noncomputable def degreeZero : CrystallineSmoothLiftTerms.term f M 0 ≅ M :=
  tensorIso (Iso.refl M)
      (SheafOfModules.RingedSite.ExteriorPower.degreeZeroIso Y.sheaf
        (CrystallineSmoothLiftTerms.oneForms f)) ≪≫
    tensorStructureIso M

/-- The first-degree term is canonically the coefficient tensor the
actual relative differential sheaf. -/
noncomputable def degreeOne : CrystallineSmoothLiftTerms.term f M 1 ≅
    moduleTensor (𝒪 := Y.sheaf) M (CrystallineSmoothLiftTerms.oneForms f) :=
  tensorIso (Iso.refl M)
    (SheafOfModules.RingedSite.ExteriorPower.degreeOneIso Y.sheaf
      (CrystallineSmoothLiftTerms.oneForms f)).symm

/-- Degree zero remains the same coefficient after restricting scalars to A. -/
noncomputable def baseDegreeZero : CrystallineSmoothLiftTerms.baseTerm f M 0 ≅
    CrystallineSmoothLiftTerms.asBaseSheaf f M :=
  (baseFunctor f).mapIso (degreeZero f M)

/-- The source connection target remains the genuine sheaf tensor after
restricting scalars, rather than a tensor of nonaffine global sections. -/
noncomputable def baseDegreeOne : CrystallineSmoothLiftTerms.baseTerm f M 1 ≅
    CrystallineSmoothLiftTerms.asBaseSheaf f
      (moduleTensor (𝒪 := Y.sheaf) M (CrystallineSmoothLiftTerms.oneForms f)) :=
  (baseFunctor f).mapIso (degreeOne f M)

end CrystallineSheafDegreeBridges
