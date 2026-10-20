module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.FlatRepresentative
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.FlatRepresentative.LowerBounded
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lower-bounded flat representatives on commutative ringed sites

This leaf specializes the abstract K-flat lower-bounded representative predicate to the
canonical tensor product associated to a commutative ring sheaf presentation.
-/

@[expose] public section

-- The native coproduct totalization is available for the fixed structure-sheaf tensor.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
  RingedSite.Hom.RingPresentation.moduleHasDerivedCategory
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open RingedSite.Hom

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The object property of admitting a K-flat, termwise-flat module-sheaf representative
supported in degrees `≥ a`. -/
@[stacks 0F1M "commutative ringed-site flat representative property"]
abbrev flatRepresentativeGE (a : ℤ) :
    ObjectProperty (ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) :=
  DerivedCategory.flatRepresentativeGE
    (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf J O)) a

/-- A derived module sheaf admits a K-flat, termwise-flat representative supported in degrees
`≥ a`. -/
abbrev HasFlatRepresentativeGE
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) (a : ℤ) : Prop :=
  flatRepresentativeGE (J := J) (O := O) a E

/-- The lower-bounded flat-representative predicate unfolds to a supported K-flat,
termwise-flat cochain representative. -/
theorem hasFlatRepresentativeGE_iff
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) (a : ℤ) :
    HasFlatRepresentativeGE E a ↔
      ∃ (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf J O)) ℤ)
          (_ : E ≅ DerivedCategory.Q.obj K),
        K.IsStrictlyGE a ∧ K.IsKFlat ∧ HomologicalComplex.IsTermwiseFlat K := sorry

variable [DerivedCategory.DerivedTensor.Right.Has
  (C := SheafOfModules.RingedSite.ringedSiteModuleCategory.{u, v, w, w} J O)]

/-- Lemma 21.46.4: lower Tor-amplitude at least `a` is equivalent to admitting a K-flat,
termwise-flat representative supported in degrees `≥ a`. -/
@[stacks 0F1M]
theorem hasTorAmplitudeGE_iff_hasFlatRepresentativeGE
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) (a : ℤ) :
    HasTorAmplitudeGE E a ↔ HasFlatRepresentativeGE E a := sorry

/-- A lower Tor-amplitude bound produces a K-flat, termwise-flat representative with the same
lower support bound. -/
theorem HasTorAmplitudeGE.hasFlatRepresentativeGE
    {E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)} {a : ℤ}
    (hE : HasTorAmplitudeGE E a) :
    HasFlatRepresentativeGE E a := sorry

/-- A K-flat, termwise-flat representative supported in degrees `≥ a` gives the corresponding
lower Tor-amplitude bound. -/
theorem HasFlatRepresentativeGE.hasTorAmplitudeGE
    {E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)} {a : ℤ}
    (hE : HasFlatRepresentativeGE E a) :
    HasTorAmplitudeGE E a := sorry

end RingedSite.Hom.ModuleDerived
