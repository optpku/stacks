module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Instances.Real.Lemmas
public import ReasLib.AlgebraicGeometry.RingedSpace.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject.Kernel
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject.LocalGeneration
public import ReasLib.Topology.Category.TopCat.Subset
public import ReasLib.Topology.Sheaves.Skyscraper

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open SheafOfModules.RingedSite

noncomputable section

namespace AlgebraicGeometry.RingedSpace.ConstantModTwo

/-- The coefficient ring `ZMod 2`. -/
def modTwoRing : CommRingCat.{0} := CommRingCat.of (ZMod 2)

/-- The real line with its usual topology. -/
abbrev realSpace : TopCat.{0} := TopCat.of ℝ

/-- The closed subset `Z = {0}` of `realSpace`. -/
def origin : Set realSpace := ({0} : Set ℝ)

/-- The inclusion `i : {0} ↪ ℝ`. -/
abbrev originInclusion : TopCat.subsetSpace origin ⟶ realSpace :=
  TopCat.subsetInclusion origin

/-- The constant sheaf of `ZMod 2` on a topological space. -/
def constantModTwo (X : TopCat.{0}) : X.Sheaf CommRingCat.{0} :=
  (constantSheaf (Opens.grothendieckTopology X) CommRingCat).obj modTwoRing

/-- Unfolding `constantModTwo` as the constant sheaf of `modTwoRing`. -/
theorem constantModTwo_def (X : TopCat.{0}) :
    constantModTwo X =
      (constantSheaf (Opens.grothendieckTopology X) CommRingCat).obj modTwoRing :=
  sorry

/-- The ringed space `(ℝ, constantModTwo realSpace)`. -/
abbrev realRingedSpace : RingedSpace.{0} :=
  (constantModTwo realSpace).toRingedSpace

/-- The ringed space `({0}, constantModTwo (subsetSpace origin))`. -/
abbrev originRingedSpace : RingedSpace.{0} :=
  (constantModTwo (TopCat.subsetSpace origin)).toRingedSpace

/-- The unit of the constant-sheaf adjunction on `{0}`, as a map from `modTwoRing` to global
sections of `constantModTwo (subsetSpace origin)`. -/
def originGlobalSections :
    modTwoRing ⟶
      ((sheafSections (Opens.grothendieckTopology (TopCat.subsetSpace origin))
          CommRingCat.{0}).obj
        (op (⊤ : Opens (TopCat.subsetSpace origin)))).obj
        (constantModTwo (TopCat.subsetSpace origin)) :=
  (constantSheafAdj (Opens.grothendieckTopology (TopCat.subsetSpace origin)) CommRingCat.{0}
      (isTerminalTop : IsTerminal (⊤ : Opens (TopCat.subsetSpace origin)))).unit.app
    modTwoRing

/-- The canonical map from `constantModTwo realSpace` to the pushforward of
`constantModTwo (subsetSpace origin)` along `originInclusion`. -/
def canonicalMap :
    constantModTwo realSpace ⟶
      (TopCat.Sheaf.pushforward CommRingCat originInclusion).obj
        (constantModTwo (TopCat.subsetSpace origin)) :=
  ((constantSheafAdj (Opens.grothendieckTopology realSpace) CommRingCat.{0}
      (isTerminalTop : IsTerminal (⊤ : Opens realSpace))).homEquiv
      modTwoRing
      ((TopCat.Sheaf.pushforward CommRingCat originInclusion).obj
        (constantModTwo (TopCat.subsetSpace origin)))).symm
    originGlobalSections

/-- The inclusion `originRingedSpace ⟶ realRingedSpace` whose structure map is `canonicalMap`. -/
def inclusion : originRingedSpace ⟶ realRingedSpace :=
  InducedCategory.homMk { base := originInclusion, c := canonicalMap.hom }

/-- `canonicalMap` is the structure-sheaf map of `inclusion`. -/
theorem canonicalMap_spec :
    canonicalMap = Hom.commRingSheafPushforwardMap inclusion :=
  sorry

/-- The kernel of `canonicalMap`, as a module over `realRingedSpace`. -/
def kernelIdeal : realRingedSpace.Modules := Hom.kernelIdealSheaf inclusion

/-- The kernel of `canonicalMap` as an `IdealSubobject` of `realRingedSpace`. -/
def kernelIdealSubobject : IdealSubobject realRingedSpace :=
  Hom.kernelIdealSubobject inclusion

/-- The kernel-ideal inclusion followed by `KernelIdeal.map canonicalMap` is zero. -/
theorem kernelIdealι_comp :
    KernelIdeal.ι canonicalMap ≫ KernelIdeal.map canonicalMap = 0 :=
  sorry

/-- A section of `constantModTwo realSpace` lies in `KernelIdeal.sectionIdeal canonicalMap`
exactly when it comes from a section of the categorical kernel. -/
theorem mem_kernelIdeal (U : (Opens realSpace)ᵒᵖ)
    (x : (constantModTwo realSpace).obj.obj U) :
    x ∈ KernelIdeal.sectionIdeal canonicalMap U ↔
      ∃ y, KernelIdeal.ιApp canonicalMap U y = x :=
  sorry

/-- Exercise 111.32.6 (1): the pushforward of `constantModTwo` along `originInclusion` is a
skyscraper sheaf. -/
@[stacks 028M]
theorem pushforward_isSkyscraper :
    TopCat.Sheaf.IsSkyscraper
      ((TopCat.Sheaf.pushforward CommRingCat originInclusion).obj
        (constantModTwo (TopCat.subsetSpace origin))) :=
  sorry

/-- Exercise 111.32.6 (2): `canonicalMap` is locally surjective. -/
@[stacks 028M, instance]
instance canonicalMap_isLocallySurjective :
    CategoryTheory.Sheaf.IsLocallySurjective canonicalMap :=
  sorry

/-- Exercise 111.32.6 (3): `kernelIdealSubobject` is an ideal sheaf of `constantModTwo realSpace`,
with sectionwise values `KernelIdeal.sectionIdeal canonicalMap`. -/
@[stacks 028M]
theorem kernelIdeal_spec (U : (Opens realSpace)ᵒᵖ) :
    IdealSheaf.sections kernelIdealSubobject U =
      KernelIdeal.sectionIdeal canonicalMap U :=
  sorry

/-- Exercise 111.32.6 (4): `kernelIdeal` is not locally generated by sections in the sense of
`SheafOfModules.IsLocallyGeneratedBySections` (Modules, Definition 17.8.1). -/
@[stacks 028M]
theorem not_isLocallyGeneratedBySections :
    ¬ SheafOfModules.IsLocallyGeneratedBySections kernelIdeal :=
  sorry

end AlgebraicGeometry.RingedSpace.ConstantModTwo

