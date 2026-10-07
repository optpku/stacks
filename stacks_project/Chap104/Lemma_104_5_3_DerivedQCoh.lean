module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import stacks_project.Chap103.Lemma_103_14_2_Ringed
public import stacks_project.Chap104.Definition_104_5_1_DerivedQCoh

/-!
# Derived categories of quasi-coherent modules on small sites

On an algebraic stack, quasi-coherent modules on the lisse-étale and
flat-fppf sites form weak Serre subcategories, so `D_QCoh` of those sites is
the cohomology-in subcategory of the corresponding unbounded derived
category of modules. This is not a Verdier quotient: unlike `QCoh(𝒪_X)` on
the large fppf site, the small-site inclusions are exact.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Weak sheafification of abelian groups exists on every slice of the
lisse-étale topology. -/
instance lisseEtaleTopology_hasWeakSheafify (X : GroupoidsOver S)
    [AlgebraicStack X] :
    ∀ x, HasWeakSheafify ((lisseEtaleTopology X).over x) AddCommGrpCat.{u} :=
  sorry

/-- On every slice of the lisse-étale topology, sheafification equivalences
are the locally bijective morphisms. -/
instance lisseEtaleTopology_wEqualsLocallyBijective (X : GroupoidsOver S)
    [AlgebraicStack X] :
    ∀ x, ((lisseEtaleTopology X).over x).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  sorry

/-- Weak sheafification of abelian groups exists on every slice of the
flat-fppf topology. -/
instance flatFppfTopology_hasWeakSheafify (X : GroupoidsOver S)
    [AlgebraicStack X] :
    ∀ x, HasWeakSheafify ((flatFppfTopology X).over x) AddCommGrpCat.{u} :=
  sorry

/-- On every slice of the flat-fppf topology, sheafification equivalences
are the locally bijective morphisms. -/
instance flatFppfTopology_wEqualsLocallyBijective (X : GroupoidsOver S)
    [AlgebraicStack X] :
    ∀ x, ((flatFppfTopology X).over x).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  sorry

/-- The category of lisse-étale `𝒪`-modules is abelian. -/
instance lisseEtaleModulesAbelian (X : GroupoidsOver S) [AlgebraicStack X] :
    Abelian (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

/-- The category of flat-fppf `𝒪`-modules is abelian. -/
instance flatFppfModulesAbelian (X : GroupoidsOver S) [AlgebraicStack X] :
    Abelian (SheafOfModules.{u} (flatFppfStructureSheaf X)) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

/-- The standard derived-category structure on lisse-étale `𝒪`-modules. -/
instance lisseEtaleModulesHasDerivedCategory (X : GroupoidsOver S)
    [AlgebraicStack X] :
    HasDerivedCategory (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) :=
  HasDerivedCategory.standard (SheafOfModules.{u} (lisseEtaleStructureSheaf X))

/-- The standard derived-category structure on flat-fppf `𝒪`-modules. -/
instance flatFppfModulesHasDerivedCategory (X : GroupoidsOver S)
    [AlgebraicStack X] :
    HasDerivedCategory (SheafOfModules.{u} (flatFppfStructureSheaf X)) :=
  HasDerivedCategory.standard (SheafOfModules.{u} (flatFppfStructureSheaf X))

/-- The unbounded derived category of modules on the lisse-étale site of an
algebraic stack. -/
abbrev ModuleDerivedLisseEtale (X : GroupoidsOver S) [AlgebraicStack X] :=
  DerivedCategory (SheafOfModules.{u} (lisseEtaleStructureSheaf X))

/-- `ModuleDerivedLisseEtale X` is the derived category of lisse-étale
`𝒪`-modules. -/
theorem ModuleDerivedLisseEtale_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    ModuleDerivedLisseEtale X =
      DerivedCategory (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) :=
  sorry

/-- The unbounded derived category of modules on the flat-fppf site of an
algebraic stack. -/
abbrev ModuleDerivedFlatFppf (X : GroupoidsOver S) [AlgebraicStack X] :=
  DerivedCategory (SheafOfModules.{u} (flatFppfStructureSheaf X))

/-- `ModuleDerivedFlatFppf X` is the derived category of flat-fppf
`𝒪`-modules. -/
theorem ModuleDerivedFlatFppf_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    ModuleDerivedFlatFppf X =
      DerivedCategory (SheafOfModules.{u} (flatFppfStructureSheaf X)) :=
  sorry

/-- Derived category of quasi-coherent modules on the lisse-étale site, as the
full subcategory of complexes whose cohomology sheaves are quasi-coherent. -/
abbrev DerivedQCohLisseEtale (X : GroupoidsOver S) [AlgebraicStack X] :=
  DerivedCategory.CohomologyIn
    (SheafOfModules.isQuasicoherent (lisseEtaleStructureSheaf X))

/-- The cohomology-in property of lisse-étale quasi-coherent modules is a
triangulated subcategory. -/
instance derivedQCohLisseEtale_isTriangulated (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (DerivedCategory.cohomologyIn
        (SheafOfModules.isQuasicoherent (lisseEtaleStructureSheaf X))).IsTriangulated :=
  sorry

/-- The lisse-étale cohomology-in subcategory is a triangulated category. -/
instance derivedQCohLisseEtale_isTriangulatedCategory (X : GroupoidsOver S)
    [AlgebraicStack X] :
    IsTriangulated (DerivedQCohLisseEtale X) :=
  inferInstance

namespace DerivedQCohLisseEtale

/-- The inclusion of `D_QCoh` of the lisse-étale site into the unbounded
derived category of lisse-étale modules. -/
abbrev inclusion (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedQCohLisseEtale X ⥤ ModuleDerivedLisseEtale X :=
  (DerivedCategory.cohomologyIn (SheafOfModules.isQuasicoherent (lisseEtaleStructureSheaf X))).ι

/-- An object of the lisse-étale derived category lies in
`DerivedQCohLisseEtale` iff every cohomology sheaf is quasi-coherent. -/
theorem mem_iff {X : GroupoidsOver S} [AlgebraicStack X]
    (E : ModuleDerivedLisseEtale X) :
    DerivedCategory.cohomologyIn (SheafOfModules.isQuasicoherent (lisseEtaleStructureSheaf X)) E ↔
      ∀ n : ℤ, SheafOfModules.isQuasicoherent (lisseEtaleStructureSheaf X)
        ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) n).obj E) :=
  sorry

/-- Every cohomology sheaf of an object of `DerivedQCohLisseEtale` is
quasi-coherent. -/
theorem homology_mem {X : GroupoidsOver S} [AlgebraicStack X]
    (H : DerivedQCohLisseEtale X) (n : ℤ) :
    SheafOfModules.isQuasicoherent (lisseEtaleStructureSheaf X)
      ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) n).obj H.obj) :=
  sorry

end DerivedQCohLisseEtale

/-- Derived category of quasi-coherent modules on the flat-fppf site, as the
full subcategory of complexes whose cohomology sheaves are quasi-coherent. -/
abbrev DerivedQCohFlatFppf (X : GroupoidsOver S) [AlgebraicStack X] :=
  DerivedCategory.CohomologyIn
    (SheafOfModules.isQuasicoherent (flatFppfStructureSheaf X))

/-- The cohomology-in property of flat-fppf quasi-coherent modules is a
triangulated subcategory. -/
instance derivedQCohFlatFppf_isTriangulated (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (DerivedCategory.cohomologyIn
        (SheafOfModules.isQuasicoherent (flatFppfStructureSheaf X))).IsTriangulated :=
  sorry

/-- The flat-fppf cohomology-in subcategory is a triangulated category. -/
instance derivedQCohFlatFppf_isTriangulatedCategory (X : GroupoidsOver S)
    [AlgebraicStack X] :
    IsTriangulated (DerivedQCohFlatFppf X) :=
  inferInstance

namespace DerivedQCohFlatFppf

/-- The inclusion of `D_QCoh` of the flat-fppf site into the unbounded derived
category of flat-fppf modules. -/
abbrev inclusion (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedQCohFlatFppf X ⥤ ModuleDerivedFlatFppf X :=
  (DerivedCategory.cohomologyIn (SheafOfModules.isQuasicoherent (flatFppfStructureSheaf X))).ι

/-- An object of the flat-fppf derived category lies in `DerivedQCohFlatFppf`
iff every cohomology sheaf is quasi-coherent. -/
theorem mem_iff {X : GroupoidsOver S} [AlgebraicStack X]
    (E : ModuleDerivedFlatFppf X) :
    DerivedCategory.cohomologyIn (SheafOfModules.isQuasicoherent (flatFppfStructureSheaf X)) E ↔
      ∀ n : ℤ, SheafOfModules.isQuasicoherent (flatFppfStructureSheaf X)
        ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (flatFppfStructureSheaf X)) n).obj E) :=
  sorry

/-- Every cohomology sheaf of an object of `DerivedQCohFlatFppf` is
quasi-coherent. -/
theorem homology_mem {X : GroupoidsOver S} [AlgebraicStack X]
    (H : DerivedQCohFlatFppf X) (n : ℤ) :
    SheafOfModules.isQuasicoherent (flatFppfStructureSheaf X)
      ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (flatFppfStructureSheaf X)) n).obj H.obj) :=
  sorry

end DerivedQCohFlatFppf

end AlgebraicGeometry.AlgebraicStack
