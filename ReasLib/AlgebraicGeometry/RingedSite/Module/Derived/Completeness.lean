/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LocalizationAway
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules.RingedSite
open IdealSheaf

noncomputable section

universe u v w z

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, z}]

/-- A derived module `K` is complete with respect to the ideal sheaf `I` when, for every
object `U` and section `f ∈ I(U)`, the localization-away tower has a zero homotopy-limit
representative in the derived category of the localized ringed site. -/
def IsDerivedCompleteWithRespectTo
    (K : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O))
    (I : Subobject (unitModule J O)) : Prop :=
  ∀ (U : C) (f : O.obj.obj (op U)),
    f ∈ sections I (op U) →
      ∃ T, HomotopyLimit.IsOf (localizationAwayTower K U f) T ∧ IsZero T

/-- Every homotopy-limit representative of a local multiplication tower is zero for a derived
complete object. -/
theorem IsDerivedCompleteWithRespectTo.isZero
    {K : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O)}
    {I : Subobject (unitModule J O)} (hK : IsDerivedCompleteWithRespectTo K I)
    (U : C) (f : O.obj.obj (op U)) (hf : f ∈ sections I (op U))
    {T : ModuleDerived.{z} ((RingedSite.ofCommRingSheaf J O).localization U)}
    (hT : HomotopyLimit.IsOf (localizationAwayTower K U f) T) : IsZero T := sorry

/-- The object property selecting derived modules complete with respect to `I`. -/
abbrev derivedCompleteObjectProperty (I : Subobject (unitModule J O)) :
    ObjectProperty (ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O)) :=
  fun K ↦ IsDerivedCompleteWithRespectTo K I

end RingedSite.Hom.ModuleDerived
