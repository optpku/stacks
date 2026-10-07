module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CohomologyIn
public import ReasLib.AlgebraicGeometry.RingedSite.Module.UniverseLift
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import stacks_project.Chap85.Lemma_85_34_2_Pullback

/-!
# Derived quasi-coherent modules on spaces-étale sites

`DerivedQCoh U` (resp. `spacesDerivedQCoh X`) is the full subcategory of
the unbounded derived category of modules on the Section 85.32 spaces-étale
ringed site of `U` (resp. `X`) whose cohomology sheaves are quasi-coherent
at coefficient universe `u + 1`. Quasi-coherence at this universe is the
isomorphism closure of carrier-lifts of the underived `ModuleCat.{u}`
quasi-coherent modules from Lemma 85.34.2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open CategoryTheory.SimplicialObject
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}}

section TotalSite

variable (U : SimplicialObject (AlgebraicSpace S))

/-- Abelian-group-valued sheafification exists on the spaces-étale total topology
at coefficient universe `u + 1`. -/
instance hasSheafify_etaleTotalRingedSite :
    HasSheafify (etaleTotalRingedSite U).siteTopology AddCommGrpCat.{u + 1} :=
  sorry

/-- Ext groups of abelian sheaves exist on the spaces-étale total topology at
coefficient universe `u + 1`. -/
instance hasExt_etaleTotalRingedSite :
    HasExt.{u + 1} (Sheaf (etaleTotalRingedSite U).siteTopology AddCommGrpCat.{u + 1}) :=
  sorry

/-- Weak sheafification of abelian groups exists on the spaces-étale total topology
at coefficient universe `u + 1`. -/
instance hasWeakSheafify_etaleTotalRingedSite :
    HasWeakSheafify (etaleTotalRingedSite U).siteTopology AddCommGrpCat.{u + 1} :=
  sorry

/-- Sheafification equivalences on the spaces-étale total topology at coefficient
universe `u + 1` are the locally bijective morphisms. -/
instance wEqualsLocallyBijective_etaleTotalRingedSite :
    (etaleTotalRingedSite U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  sorry

/-- The standard derived-category structure on modules on `U_spaces,étale` at
coefficient universe `u + 1`. -/
instance etaleTotalRingedSite_hasDerivedCategory :
    HasDerivedCategory (RingedSite.ModuleCat.{u + 1} (etaleTotalRingedSite U)) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1} (etaleTotalRingedSite U)

/-- The object property of quasi-coherent module sheaves on `U_spaces,étale` at
coefficient universe `u + 1`. -/
def quasiCoherentProperty :
    ObjectProperty (RingedSite.ModuleCat.{u + 1} (etaleTotalRingedSite U)) :=
  fun M ↦ ∃ (N : RingedSite.ModuleCat.{u} (etaleTotalRingedSite U)),
    quasiCoherentModuleProperty U N ∧
      Nonempty (M ≅ RingedSite.Module.carrierLift (etaleTotalRingedSite U) N)

/-- A module sheaf on `U_spaces,étale` at universe `u + 1` lies in
`quasiCoherentProperty U` if and only if it is isomorphic to the carrier lift of a
quasi-coherent module sheaf on `etaleTotalRingedSite U`. -/
theorem mem_quasiCoherentProperty_iff
    {M : RingedSite.ModuleCat.{u + 1} (etaleTotalRingedSite U)} :
    quasiCoherentProperty U M ↔
      ∃ (N : RingedSite.ModuleCat.{u} (etaleTotalRingedSite U)),
        quasiCoherentModuleProperty U N ∧
          Nonempty (M ≅ RingedSite.Module.carrierLift (etaleTotalRingedSite U) N) :=
  sorry

/-- The carrier lift of a quasi-coherent module on `U_spaces,étale` is quasi-coherent
at universe `u + 1`. -/
theorem carrierLift_mem_quasiCoherentProperty
    {N : RingedSite.ModuleCat.{u} (etaleTotalRingedSite U)}
    (hN : quasiCoherentModuleProperty U N) :
    quasiCoherentProperty U (RingedSite.Module.carrierLift (etaleTotalRingedSite U) N) :=
  sorry

/-- The derived category `D_QCoh(𝒪_U)` of modules with quasi-coherent cohomology on
the spaces-étale total ringed site. -/
abbrev DerivedQCoh :=
  RingedSite.Hom.ModuleCohomologyIn.{u + 1, u + 1, u + 1, u}
    (etaleTotalRingedSite U) (quasiCoherentProperty U)

namespace DerivedQCoh

/-- The inclusion of `D_QCoh(𝒪_U)` into the unbounded derived category of modules on
`U_spaces,étale`. -/
abbrev inclusion :
    DerivedQCoh U ⥤ RingedSite.Hom.ModuleDerived.{u + 1} (etaleTotalRingedSite U) :=
  (RingedSite.Hom.moduleCohomologyIn.{u + 1, u + 1, u + 1, u}
    (etaleTotalRingedSite U) (quasiCoherentProperty U)).ι

/-- An object of `D(𝒪_U)` lies in `DerivedQCoh U` if and only if every cohomology
sheaf is quasi-coherent at universe `u + 1`. -/
theorem mem_iff (E : RingedSite.Hom.ModuleDerived.{u + 1} (etaleTotalRingedSite U)) :
    RingedSite.Hom.moduleCohomologyIn.{u + 1, u + 1, u + 1, u}
        (etaleTotalRingedSite U) (quasiCoherentProperty U) E ↔
      ∀ n : ℤ, quasiCoherentProperty U
        ((DerivedCategory.homologyFunctor
          (RingedSite.ModuleCat.{u + 1} (etaleTotalRingedSite U)) n).obj E) :=
  sorry

end DerivedQCoh

end TotalSite

section SpacesSite

variable (X : AlgebraicSpace S)

/-- Abelian-group-valued sheafification exists on the spaces-étale topology of an
algebraic space at coefficient universe `u + 1`. -/
instance hasSheafify_spacesRingedSite :
    HasSheafify (spacesRingedSite X).siteTopology AddCommGrpCat.{u + 1} :=
  sorry

/-- Ext groups of abelian sheaves exist on the spaces-étale topology of an algebraic
space at coefficient universe `u + 1`. -/
instance hasExt_spacesRingedSite :
    HasExt.{u + 1} (Sheaf (spacesRingedSite X).siteTopology AddCommGrpCat.{u + 1}) :=
  sorry

/-- Weak sheafification of abelian groups exists on the spaces-étale topology of an
algebraic space at coefficient universe `u + 1`. -/
instance hasWeakSheafify_spacesRingedSite :
    HasWeakSheafify (spacesRingedSite X).siteTopology AddCommGrpCat.{u + 1} :=
  sorry

/-- Sheafification equivalences on the spaces-étale topology of an algebraic space at
coefficient universe `u + 1` are the locally bijective morphisms. -/
instance wEqualsLocallyBijective_spacesRingedSite :
    (spacesRingedSite X).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  sorry

/-- The standard derived-category structure on modules on `X_spaces,étale` at
coefficient universe `u + 1`. -/
instance spacesRingedSite_hasDerivedCategory :
    HasDerivedCategory (RingedSite.ModuleCat.{u + 1} (spacesRingedSite X)) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1} (spacesRingedSite X)

/-- The object property of quasi-coherent module sheaves on `X_spaces,étale` at
coefficient universe `u + 1`. -/
def spacesQuasiCoherentProperty :
    ObjectProperty (RingedSite.ModuleCat.{u + 1} (spacesRingedSite X)) :=
  fun M ↦ ∃ (N : RingedSite.ModuleCat.{u} (spacesRingedSite X)),
    spacesQuasiCoherentModuleProperty X N ∧
      Nonempty (M ≅ RingedSite.Module.carrierLift (spacesRingedSite X) N)

/-- A module sheaf on `X_spaces,étale` at universe `u + 1` lies in
`spacesQuasiCoherentProperty X` if and only if it is isomorphic to the carrier lift
of a quasi-coherent module sheaf on `spacesRingedSite X`. -/
theorem mem_spacesQuasiCoherentProperty_iff
    {M : RingedSite.ModuleCat.{u + 1} (spacesRingedSite X)} :
    spacesQuasiCoherentProperty X M ↔
      ∃ (N : RingedSite.ModuleCat.{u} (spacesRingedSite X)),
        spacesQuasiCoherentModuleProperty X N ∧
          Nonempty (M ≅ RingedSite.Module.carrierLift (spacesRingedSite X) N) :=
  sorry

/-- The carrier lift of a quasi-coherent module on `X_spaces,étale` is quasi-coherent
at universe `u + 1`. -/
theorem carrierLift_mem_spacesQuasiCoherentProperty
    {N : RingedSite.ModuleCat.{u} (spacesRingedSite X)}
    (hN : spacesQuasiCoherentModuleProperty X N) :
    spacesQuasiCoherentProperty X (RingedSite.Module.carrierLift (spacesRingedSite X) N) :=
  sorry

/-- The derived category `D_QCoh(𝒪_X)` of modules with quasi-coherent cohomology on
the spaces-étale ringed site. -/
abbrev spacesDerivedQCoh :=
  RingedSite.Hom.ModuleCohomologyIn.{u + 1, u + 1, u + 1, u}
    (spacesRingedSite X) (spacesQuasiCoherentProperty X)

namespace spacesDerivedQCoh

/-- The inclusion of `D_QCoh(𝒪_X)` into the unbounded derived category of modules on
`X_spaces,étale`. -/
abbrev inclusion :
    spacesDerivedQCoh X ⥤ RingedSite.Hom.ModuleDerived.{u + 1} (spacesRingedSite X) :=
  (RingedSite.Hom.moduleCohomologyIn.{u + 1, u + 1, u + 1, u}
    (spacesRingedSite X) (spacesQuasiCoherentProperty X)).ι

/-- An object of `D(𝒪_X)` lies in `spacesDerivedQCoh X` if and only if every
cohomology sheaf is quasi-coherent at universe `u + 1`. -/
theorem mem_iff (E : RingedSite.Hom.ModuleDerived.{u + 1} (spacesRingedSite X)) :
    RingedSite.Hom.moduleCohomologyIn.{u + 1, u + 1, u + 1, u}
        (spacesRingedSite X) (spacesQuasiCoherentProperty X) E ↔
      ∀ n : ℤ, spacesQuasiCoherentProperty X
        ((DerivedCategory.homologyFunctor
          (RingedSite.ModuleCat.{u + 1} (spacesRingedSite X)) n).obj E) :=
  sorry

end spacesDerivedQCoh

end SpacesSite

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
