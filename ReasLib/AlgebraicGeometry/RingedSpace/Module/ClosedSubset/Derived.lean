/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ClosedSubset.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.SectionsWithSupport
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.ProjectionFormula.ClosedEmbedding
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Equivalence
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Exact
public import ReasLib.CategoryTheory.Monoidal.Adjunction.SupportedTensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived module functors on closed subsets of ringed spaces

This file specializes the coefficient-generic bundled closed-subset API to the structure sheaf of
a ringed space. Mathematical constructions remain owned by
`SheafOfModules.ClosedSubset.Derived`; this namespace only supplies the ringed-space vocabulary.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ClosedSubset

variable (X : RingedSpace.{u}) (Z : Closeds X)

/-- Closed-subset module sheaves use their standard unbounded derived category. -/
@[reducible, instance]
noncomputable def modulesHasDerivedCategory :
    HasDerivedCategory (SheafOfModules.ClosedSubset.Modules X.ringCatSheaf Z) :=
  HasDerivedCategory.standard _

/-- The unbounded derived category of modules on a bundled closed subset of a ringed space. -/
@[stacks 0A3B "ringed-space closed-subset module derived category"]
abbrev ModuleDerived :=
  SheafOfModules.ClosedSubset.ModuleDerived X.ringCatSheaf Z

/-- The unbounded derived category of modules on the intrinsic ringed subspace carried by a
bundled closed subset. -/
@[stacks 0G75 "intrinsic closed-subspace module derived category"]
abbrev IntrinsicModuleDerived :=
  DerivedCategory (ringedSpace X Z).Modules

/-- The canonical derived equivalence between the intrinsic ringed-subspace presentation and the
restricted-ring-sheaf presentation of modules on a closed subset. -/
@[stacks 0G75 "closed-subspace derived presentation equivalence"]
noncomputable abbrev moduleDerivedEquivalence
    [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    IntrinsicModuleDerived X Z ≌ ModuleDerived X Z :=
  (moduleEquivalence X Z).mapDerivedCategory

namespace Inclusion

/-- The intrinsic closed-subspace direct image preserves finite limits, transported from the
canonical closed-subset presentation.  This is a named proof owner rather than a global instance,
so unrelated pushforward searches do not try to synthesize the sheafification hypothesis. -/
@[stacks 0G75 "finite-limit preservation for intrinsic closed-subspace pushforward"]
theorem pushforwardPreservesFiniteLimits
    [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    PreservesFiniteLimits (RingedSpace.Hom.pushforward (inclusionHom X Z)) := sorry

/-- The intrinsic closed-subspace direct image preserves finite colimits, transported from the
canonical closed-subset presentation.  This is kept out of global typeclass search for the same
reason as `pushforwardPreservesFiniteLimits`. -/
@[stacks 0G75 "finite-colimit preservation for intrinsic closed-subspace pushforward"]
theorem pushforwardPreservesFiniteColimits
    [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    PreservesFiniteColimits (RingedSpace.Hom.pushforward (inclusionHom X Z)) := sorry

/-- The intrinsic closed-subspace direct image bundled as an exact functor.  This is the canonical
owner consumed by exact-derived constructions without installing global preservation instances. -/
@[stacks 0G75 "exact intrinsic closed-subspace direct image"]
noncomputable def exact
    [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    (ringedSpace X Z).Modules ⥤ₑ X.Modules :=
  ⟨RingedSpace.Hom.pushforward (inclusionHom X Z),
    pushforwardPreservesFiniteLimits X Z, pushforwardPreservesFiniteColimits X Z⟩

/-- The total derived pullback and pushforward along an intrinsic closed-subspace inclusion satisfy
the two absolute-derived conditions needed to form their canonical adjunction. -/
theorem derivedAdjunctionHasPair
    [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (inclusionHom X Z)) := sorry

/-- The canonical derived pullback-pushforward adjunction for an intrinsic closed-subspace
inclusion. -/
noncomputable def derivedAdjunction
    [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    RingedSpace.modulePullbackDerived (inclusionHom X Z) ⊣
      RingedSpace.moduleDerivedPushforward (inclusionHom X Z) :=
  @RingedSpace.modulePullbackDerivedPushforwardAdjunction _ _
    (inclusionHom X Z) _ _ _ _ _ _ _ (derivedAdjunctionHasPair X Z)

/-- The canonical derived pullback-pushforward adjunction for a bundled closed-subspace inclusion
satisfies the right projection formula. -/
@[reducible, stacks 0G75 "projection formula for a bundled closed-subspace inclusion"]
noncomputable def projectionFormula
    [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends (ringedSpace X Z)]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends (ringedSpace X Z)]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization (ringedSpace X Z)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived (inclusionHom X Z))] :
    (derivedAdjunction X Z).ProjectionFormula :=
  @RingedSpace.ModuleDerived.ClosedEmbedding.projectionFormula _ _ _ _ _ _ _ _
    (inclusionHom X Z) (derivedAdjunctionHasPair X Z) _ _ _ _
      (inclusionHom_isClosedEmbedding X Z)

end Inclusion

namespace Pushforward

/-- Exact direct image from a bundled closed subset on unbounded derived module categories. -/
@[stacks 0A3B "ringed-space derived closed-subset pushforward"]
noncomputable abbrev derived :
    ModuleDerived X Z ⥤ DerivedCategory X.Modules :=
  SheafOfModules.ClosedSubset.Derived.pushforward X.ringCatSheaf Z

/-- The canonical localization square for derived direct image from a closed subset. -/
@[stacks 0A3B "ringed-space derived closed-subset pushforward localization square"]
noncomputable abbrev factors :=
  SheafOfModules.ClosedSubset.Derived.pushforwardFactors X.ringCatSheaf Z

/-- The cochain-level direct image followed by localization. -/
@[stacks 0A3B "ringed-space derived closed-subset pushforward cochain localization"]
abbrev toDerived :=
  SheafOfModules.ClosedSubset.Derived.pushforwardToDerived X.ringCatSheaf Z

/-- The total left-derived presentation of exact direct image from a closed subset. -/
@[stacks 0A3B "ringed-space total left-derived closed-subset pushforward"]
noncomputable abbrev totalLeft :=
  SheafOfModules.ClosedSubset.Derived.pushforwardTotalLeft X.ringCatSheaf Z

/-- The comparison counit for the total left-derived direct-image presentation. -/
@[stacks 0A3B "ringed-space total left-derived pushforward counit"]
noncomputable abbrev totalLeftCounit :=
  SheafOfModules.ClosedSubset.Derived.pushforwardTotalLeftCounit X.ringCatSheaf Z

/-- The canonical isomorphism from total left-derived direct image to exact derived direct
image. -/
@[stacks 0A3B "ringed-space total left-derived pushforward comparison"]
noncomputable abbrev totalLeftIso :=
  SheafOfModules.ClosedSubset.Derived.pushforwardTotalLeftIso X.ringCatSheaf Z

/-- Derived direct image from a closed subset is fully faithful. -/
@[stacks 0A3B "ringed-space derived closed-subset pushforward fully faithful"]
noncomputable abbrev fullyFaithful :=
  SheafOfModules.ClosedSubset.Derived.pushforwardFullyFaithful X.ringCatSheaf Z

end Pushforward

namespace SectionsWithSupport

/-- The cochain-level supported-sections functor followed by localization. -/
@[stacks 0A3B "ringed-space supported-sections cochain localization"]
abbrev toDerived :=
  SheafOfModules.ClosedSubset.Derived.sectionsWithSupportToDerived X.ringCatSheaf Z

/-- The total right derived functor of module sections supported on a bundled closed subset. -/
@[stacks 0A3B "ringed-space derived module sections with support"]
noncomputable abbrev derived :
    DerivedCategory X.Modules ⥤ ModuleDerived X Z :=
  SheafOfModules.ClosedSubset.Derived.sectionsWithSupport X.ringCatSheaf Z

/-- The canonical cochain-level unit for derived module sections with support. -/
@[stacks 0A3B "ringed-space supported-sections derived unit"]
noncomputable abbrev unit :=
  SheafOfModules.ClosedSubset.Derived.sectionsWithSupportUnit X.ringCatSheaf Z

end SectionsWithSupport

namespace Derived

/-- The canonical adjunction between derived direct image and derived sections with support. -/
@[stacks 0A3B "ringed-space derived closed-subset adjunction"]
noncomputable abbrev adjunction :
    Pushforward.derived X Z ⊣ SectionsWithSupport.derived X Z :=
  SheafOfModules.ClosedSubset.Derived.adjunction X.ringCatSheaf Z

/-- Derived direct image from a bundled closed subset is canonically a left adjoint. -/
@[stacks 0A3B "ringed-space derived closed-subset pushforward is a left adjoint"]
instance pushforwardIsLeftAdjoint :
    Functor.IsLeftAdjoint (Pushforward.derived X Z) := sorry

/-- Derived sections with support in a bundled closed subset are canonically a right adjoint. -/
@[stacks 0A3B "ringed-space derived sections with support are a right adjoint"]
instance sectionsWithSupportIsRightAdjoint :
    Functor.IsRightAdjoint (SectionsWithSupport.derived X Z) := sorry

end Derived

namespace Intrinsic

namespace Pullback

/-- Derived restriction from an ambient ringed space to its intrinsic closed ringed subspace. -/
@[stacks 0G75 "derived restriction to a closed ringed subspace"]
noncomputable abbrev derived :
    DerivedCategory X.Modules ⥤ IntrinsicModuleDerived X Z :=
  RingedSpace.modulePullbackDerived (inclusionHom X Z)

end Pullback

end Intrinsic

namespace Pullback

/-- Derived restriction to the legacy closed-subset module presentation.  The intrinsic pullback is
the canonical geometric owner; this view transports it across the presentation equivalence used by
`ModuleDerived X Z` and is provided only when that equivalence is available. -/
@[stacks 0G75 "legacy derived restriction to a closed subset"]
noncomputable abbrev derived
    [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    DerivedCategory X.Modules ⥤ ModuleDerived X Z :=
  Intrinsic.Pullback.derived X Z ⋙ (moduleDerivedEquivalence X Z).functor

end Pullback

namespace Intrinsic

namespace Pushforward

/-- The exact functor underlying the transported intrinsic closed-subspace direct image. -/
@[stacks 0G75 "exact intrinsic closed-subspace pushforward"]
noncomputable abbrev exact
    [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    (ringedSpace X Z).Modules ⥤ₑ X.Modules :=
  (ExactFunctor.of (moduleEquivalence X Z).functor).comp
    (ExactFunctor.of (SheafOfModules.ClosedSubset.pushforward X.ringCatSheaf Z))

/-- The exact-functor isomorphism comparing transported and intrinsic closed-subspace pushforward. -/
@[stacks 0G75 "exact intrinsic pushforward comparison"]
noncomputable abbrev exactIso
    [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    exact X Z ≅ Inclusion.exact X Z :=
  ObjectProperty.isoMk (exactFunctor (ringedSpace X Z).Modules X.Modules)
    (Inclusion.pushforwardIso X Z)

/-- Derived direct image from the intrinsic closed-subspace presentation, obtained by transporting
the exact closed-subset direct image across the canonical derived presentation equivalence. -/
@[stacks 0G75 "intrinsic closed-subspace derived direct image"]
noncomputable abbrev derived
    [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    IntrinsicModuleDerived X Z ⥤ DerivedCategory X.Modules :=
  (moduleDerivedEquivalence X Z).functor ⋙
    ClosedSubset.Pushforward.derived X Z

/-- The exact-derived comparison from the transported closed-subset presentation to the intrinsic
pushforward induced directly by the underived ringed-space morphism. -/
@[stacks 0G75 "exact-derived intrinsic pushforward comparison"]
noncomputable def exactComparison
    [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    derived X Z ≅ (Inclusion.exact X Z).obj.mapDerivedCategory :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (moduleEquivalence X Z).functor)
      (ExactFunctor.of (SheafOfModules.ClosedSubset.pushforward X.ringCatSheaf Z))).symm ≪≫
    ExactFunctor.MapDerivedCategory.mapIso (exactIso X Z)

/-- The canonical comparison between the direct exact-derived presentation and the homotopy total
right-derived presentation of intrinsic pushforward. -/
@[stacks 0G75 "homotopy-derived intrinsic pushforward comparison"]
noncomputable abbrev homotopyComparison
    [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    (Inclusion.exact X Z).obj.mapDerivedCategory ≅
      RingedSpace.moduleDerivedPushforward (inclusionHom X Z) :=
  CategoryTheory.Functor.RightDerived.Exact.homotopyIso
    (Inclusion.exact X Z).obj

/-- The canonical comparison from transported intrinsic pushforward to the ordinary notation
`R(i)_*` on derived categories. -/
@[stacks 0G75 "intrinsic pushforward to total right-derived comparison"]
noncomputable def comparison
    [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    derived X Z ≅ RingedSpace.moduleDerivedPushforward (inclusionHom X Z) :=
  exactComparison X Z ≪≫ homotopyComparison X Z

end Pushforward

namespace SectionsWithSupport

/-- Derived sections with support valued in the intrinsic closed-subspace presentation. -/
@[stacks 0G75 "intrinsic derived sections with support"]
noncomputable abbrev derived
    [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    DerivedCategory X.Modules ⥤ IntrinsicModuleDerived X Z :=
  ClosedSubset.SectionsWithSupport.derived X Z ⋙
    (moduleDerivedEquivalence X Z).inverse

end SectionsWithSupport

namespace Derived

/-- The intrinsic closed-subspace direct image is left adjoint to intrinsic derived sections with
support. -/
@[stacks 0G75 "intrinsic closed-subspace derived adjunction"]
noncomputable def adjunction
    [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    Pushforward.derived X Z ⊣ SectionsWithSupport.derived X Z :=
  (moduleDerivedEquivalence X Z).toAdjunction.comp
    (ClosedSubset.Derived.adjunction X Z)

/-- The ordinary total right-derived direct image is left adjoint to intrinsic derived sections
with support.  This is the adjunction used by projection-formula and tensor-with-support APIs. -/
@[stacks 0G75 "total right-derived closed-subspace adjunction"]
noncomputable def pushforwardAdjunction
    [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    RingedSpace.moduleDerivedPushforward (inclusionHom X Z) ⊣
      SectionsWithSupport.derived X Z :=
  (adjunction X Z).ofNatIsoLeft (Intrinsic.Pushforward.comparison X Z)

end Derived

namespace Support

variable [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
  (forget₂ CommRingCat RingCat.{u})]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends X]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization X]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends (ringedSpace X Z)]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends (ringedSpace X Z)]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization (ringedSpace X Z)]
variable [Functor.Monoidal
  (RingedSpace.modulePullbackDerived (inclusionHom X Z))]

/-- The intrinsic tensor product with closed support, natural in both ambient derived modules. -/
@[stacks 0G75 "intrinsic tensor product with closed support"]
noncomputable abbrev tensorNatTrans :
    Functor.prod (Intrinsic.Pullback.derived X Z)
          (Intrinsic.SectionsWithSupport.derived X Z) ⋙
        MonoidalCategory.tensor (IntrinsicModuleDerived X Z) ⟶
      MonoidalCategory.tensor (RingedSpace.ModuleDerived X) ⋙
        Intrinsic.SectionsWithSupport.derived X Z :=
  @CategoryTheory.Adjunction.supportTensorNatTrans _ _ _ _ _ _ _ _ _
    (Inclusion.derivedAdjunction X Z) (Derived.pushforwardAdjunction X Z) _
      (Inclusion.projectionFormula X Z)

/- The pushforward-side view is kept beside `tensorNatTrans`: it is often the more convenient
   interface when a calculation starts in the ambient derived category. -/
/-- The ambient tensor map with support, natural in both ambient arguments. -/
@[stacks 0G75 "ambient tensor map with support natural transformation"]
noncomputable abbrev tensorPushNatTrans :
    (Functor.prod (Intrinsic.Pullback.derived X Z)
          (Intrinsic.SectionsWithSupport.derived X Z) ⋙
        MonoidalCategory.tensor (IntrinsicModuleDerived X Z)) ⋙
      RingedSpace.moduleDerivedPushforward (inclusionHom X Z) ⟶
      MonoidalCategory.tensor (RingedSpace.ModuleDerived X) :=
  @CategoryTheory.Adjunction.supportTensorPushNatTrans _ _ _ _ _ _ _ _ _
    (Inclusion.derivedAdjunction X Z) (Derived.pushforwardAdjunction X Z) _
      (Inclusion.projectionFormula X Z)

/-- The supported tensor transformation with a fixed ambient left factor. -/
@[stacks 0G75 "fixed-left tensor with closed support"]
noncomputable abbrev tensorLeftNatTrans (K : RingedSpace.ModuleDerived X) :
    Intrinsic.SectionsWithSupport.derived X Z ⋙
        MonoidalCategory.tensorLeft ((Intrinsic.Pullback.derived X Z).obj K) ⟶
      MonoidalCategory.tensorLeft K ⋙ Intrinsic.SectionsWithSupport.derived X Z :=
  @CategoryTheory.Adjunction.supportTensorLeftNatTrans _ _ _ _ _ _ _ _ _
    (Inclusion.derivedAdjunction X Z) (Derived.pushforwardAdjunction X Z) _
      (Inclusion.projectionFormula X Z) K

/-- The supported tensor transformation with a fixed supported right factor. -/
@[stacks 0G75 "fixed-right tensor with closed support"]
noncomputable abbrev tensorRightNatTrans (M : RingedSpace.ModuleDerived X) :
    Intrinsic.Pullback.derived X Z ⋙
        MonoidalCategory.tensorRight
          ((Intrinsic.SectionsWithSupport.derived X Z).obj M) ⟶
      MonoidalCategory.tensorRight M ⋙ Intrinsic.SectionsWithSupport.derived X Z :=
  @CategoryTheory.Adjunction.supportTensorRightNatTrans _ _ _ _ _ _ _ _ _
    (Inclusion.derivedAdjunction X Z) (Derived.pushforwardAdjunction X Z) _
      (Inclusion.projectionFormula X Z) M

/-- The canonical tensor product with support on a bundled closed subspace. -/
@[stacks 0G75 "intrinsic tensor product with closed support"]
noncomputable abbrev tensor (K M : RingedSpace.ModuleDerived X) :
    (Intrinsic.Pullback.derived X Z).obj K ⊗
        (Intrinsic.SectionsWithSupport.derived X Z).obj M ⟶
      (Intrinsic.SectionsWithSupport.derived X Z).obj (K ⊗ M) :=
  (tensorNatTrans X Z).app (K, M)

/-- The ambient tensor map whose mate is `Support.tensor`. -/
@[stacks 0G75 "ambient tensor product with closed support"]
noncomputable abbrev tensorPush (K M : RingedSpace.ModuleDerived X) :
    (RingedSpace.moduleDerivedPushforward (inclusionHom X Z)).obj
        ((Intrinsic.Pullback.derived X Z).obj K ⊗
          (Intrinsic.SectionsWithSupport.derived X Z).obj M) ⟶
      K ⊗ M :=
  @CategoryTheory.Adjunction.supportTensorPush _ _ _ _ _ _ _ _ _
    (Inclusion.derivedAdjunction X Z) (Derived.pushforwardAdjunction X Z) _
      (Inclusion.projectionFormula X Z) K M

/-- Applying total right-derived direct image to the intrinsic tensor-with-support map and then the
support counit recovers `Support.tensorPush`. -/
@[stacks 0G75 "intrinsic tensor product with support counit equation"]
theorem tensor_comp_counit (K M : RingedSpace.ModuleDerived X) :
    (RingedSpace.moduleDerivedPushforward (inclusionHom X Z)).map
        (tensor X Z K M) ≫
      (Derived.pushforwardAdjunction X Z).counit.app (K ⊗ M) =
    tensorPush X Z K M := sorry

end Support

end Intrinsic

end AlgebraicGeometry.RingedSpace.ClosedSubset
