module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.ExtensionByZero.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Pushforward.Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparing extension by zero with open pushforward

For an open immersion `j : U ⟶ X`, the inverse of the unit `F ⟶ j^*j_!F`, followed by the
adjunction `j^* ⊣ j_*`, gives the canonical comparison `j_!F ⟶ j_*F`. This file owns that map at
the underived and derived levels, so support theorems can refer to a stable natural transformation
instead of rebuilding its mate objectwise.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.OpenSubspace.ExtensionByZero

/-- The component `j_!F ⟶ j_*F` of the canonical comparison for an open subspace. -/
@[stacks 08DF "extension by zero to open pushforward"]
noncomputable def toPushforwardApp
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    (F : openSubspaceModuleCategory X U) :
    (moduleExtensionByZeroFromOpen X U).obj F ⟶ (modulePushforwardFromOpen U).obj F :=
  (OpenSubspace.Pushforward.adjunction X U).homEquiv
    ((moduleExtensionByZeroFromOpen X U).obj F) F
    ((asIso ((adjunction X U).unit.app F)).inv)

/-- The underived comparison components commute with morphisms of modules on the open
subspace. -/
theorem toPushforwardApp_naturality
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    {F G : openSubspaceModuleCategory X U} (f : F ⟶ G) :
    (moduleExtensionByZeroFromOpen X U).map f ≫ toPushforwardApp X U G =
      toPushforwardApp X U F ≫ (modulePushforwardFromOpen U).map f := sorry

/-- The canonical natural transformation `j_! ⟶ j_*` for modules on an open subspace. -/
@[stacks 08DF "extension by zero to open pushforward natural transformation"]
noncomputable def toPushforward
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    moduleExtensionByZeroFromOpen X U ⟶ modulePushforwardFromOpen U where
  app := toPushforwardApp X U
  naturality := fun {_ _} f ↦ toPushforwardApp_naturality X U f

/-- The component `j_!F ⟶ Rj_*F` of the canonical comparison on derived categories. -/
@[stacks 08DF "derived extension by zero to open pushforward"]
noncomputable def derivedToPushforwardApp
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    (F : moduleDerivedOnOpen X U) :
    (moduleExtensionByZeroFromOpenDerived X U).obj F ⟶
      (modulePushforwardFromOpenDerived U).obj F :=
  (OpenSubspace.Pushforward.derivedAdjunction X U).homEquiv
    ((moduleExtensionByZeroFromOpenDerived X U).obj F) F
    ((asIso ((derivedAdjunction X U).unit.app F)).inv)

/-- The derived comparison components commute with morphisms of derived modules on the open
subspace. -/
theorem derivedToPushforwardApp_naturality
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    {F G : moduleDerivedOnOpen X U} (f : F ⟶ G) :
    (moduleExtensionByZeroFromOpenDerived X U).map f ≫ derivedToPushforwardApp X U G =
      derivedToPushforwardApp X U F ≫ (modulePushforwardFromOpenDerived U).map f := sorry

/-- The canonical natural transformation `j_! ⟶ Rj_*` on unbounded derived categories. -/
@[stacks 08DF "derived extension by zero to open pushforward natural transformation"]
noncomputable def derivedToPushforward
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    moduleExtensionByZeroFromOpenDerived X U ⟶ modulePushforwardFromOpenDerived U where
  app := derivedToPushforwardApp X U
  naturality := fun {_ _} f ↦ derivedToPushforwardApp_naturality X U f

-- Both natural transformations have explicit objectwise maps. Any `sorryAx` is confined to the
-- naturality laws and to the invertibility proof fields of the extension-restriction units.

end AlgebraicGeometry.RingedSpace.OpenSubspace.ExtensionByZero
