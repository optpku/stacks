module

public import ReasLib.CategoryTheory.Adjunction.ReflectiveColimits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
noncomputable section
universe u v w

namespace SheafOfModules.RingedSite.Tensor
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}}

/-- Tensor/sheafification comparison built from the supplied monoidal maps and the actual
sheafification counit. No tensor-preservation proposition selects this isomorphism. -/
def rightComparison (G : ringedSiteModuleCategory.{u, v, w, w} J O) :
    tensorRight ((SheafOfModules.forget (ringSheaf J O) ⋙
      PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)).obj G) ⋙
        PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj) ≅
    PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj) ⋙ tensorRight G :=
  (Functor.Monoidal.commTensorRight
    (PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj)) _).symm ≪≫
    Functor.isoWhiskerLeft _ ((tensoringRight _).mapIso
      ((asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O).obj)).counit).app G))

/-- Actual colimit witness for tensoring a sheaf colimit of a finite diagram. Its construction
uses pointwise module-presheaf colimits and the actual sheafification adjunction. -/
def rightMapColimit {K : Type} [SmallCategory K] [FinCategory K]
    {F : K ⥤ ringedSiteModuleCategory.{u, v, w, w} J O} {c : Cocone F}
    (hc : IsColimit c) (G : ringedSiteModuleCategory.{u, v, w, w} J O) :
    IsColimit ((tensorRight G).mapCocone c) := by
  let L := PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj)
  let R := SheafOfModules.forget (ringSheaf J O) ⋙
    PresheafOfModules.restrictScalars (𝟙 (ringSheaf J O).obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J O).obj)
  let S := tensorRight (R.obj G)
  letI : PreservesColimitsOfSize.{w, w} S :=
    inferInstanceAs (PreservesColimitsOfSize.{w, w}
      (tensorRight (R.obj G) : PresheafOfModules.{w} (O.obj ⋙ forget₂ _ _) ⥤ _))
  letI : PreservesFiniteColimits S := PreservesColimitsOfSize.preservesFiniteColimits S
  exact adj.reflectiveMapColimitWitness (asIso adj.counit) S (tensorRight G)
    (rightComparison G) (fun h ↦ isColimitOfPreserves S h) hc

/-- Finite-colimit preservation packaged only after constructing its actual witnesses. -/
theorem rightPreservesFiniteColimits (G : ringedSiteModuleCategory.{u, v, w, w} J O) :
    PreservesFiniteColimits (tensorRight G) where
  preservesFiniteColimits _ _ _ :=
    { preservesColimit := { preserves := fun h ↦ ⟨rightMapColimit h G⟩ } }

end SheafOfModules.RingedSite.Tensor
