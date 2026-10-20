module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.LocalModel
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Perfect complexes on ringed spaces

Perfectness is the specialization of the ringed-site complex property to the canonical site of
open subsets.  This facade does not import the derived category of module sheaves.
-/

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.CochainComplex

variable {X : RingedSpace.{u}}

/-- Complexes of `𝒪_X`-modules admitting a strictly perfect quasi-isomorphic model. -/
abbrev hasStrictlyPerfectModel :
    ObjectProperty (_root_.CochainComplex (Modules X) ℤ) :=
  SheafOfModules.CochainComplex.hasStrictlyPerfectModel (R := X.ringCatSheaf)

/-- A complex of `𝒪_X`-modules has a strictly perfect quasi-isomorphic model. -/
abbrev HasStrictlyPerfectModel
    (E : _root_.CochainComplex (Modules X) ℤ) : Prop :=
  hasStrictlyPerfectModel (X := X) E

/-- Perfect complexes of `𝒪_X`-modules, as an object property. -/
abbrev perfect : ObjectProperty (_root_.CochainComplex (Modules X) ℤ) :=
  SheafOfModules.CochainComplex.perfect (R := X.ringCatSheaf)

/-- A complex of `𝒪_X`-modules is perfect when it is locally quasi-isomorphic to strictly
perfect complexes. -/
@[stacks 08CM "(1)"]
abbrev IsPerfect (E : _root_.CochainComplex (Modules X) ℤ) : Prop :=
  perfect (X := X) E

/-- Perfect complexes of `𝒪_X`-modules, as a full subcategory. -/
@[stacks 08CM "(1), full subcategory"]
abbrev Perfect :=
  (perfect (X := X)).FullSubcategory

namespace Perfect

/-- The canonical inclusion of perfect complexes of `𝒪_X`-modules. -/
abbrev ι : Perfect (X := X) ⥤ _root_.CochainComplex (Modules X) ℤ :=
  ObjectProperty.ι _

end Perfect

/-- Transport perfectness along an isomorphism of complexes of `𝒪_X`-modules. -/
theorem IsPerfect.of_iso
    {E F : _root_.CochainComplex (Modules X) ℤ}
    (hE : IsPerfect E) (e : E ≅ F) :
    IsPerfect F := sorry

/-- A strictly perfect model on a ringed space is preserved by isomorphism. -/
@[stacks 08CM "isomorphism stability of strictly perfect models"]
theorem HasStrictlyPerfectModel.of_iso
    {E F : _root_.CochainComplex (Modules X) ℤ}
    (hE : HasStrictlyPerfectModel E) (e : E ≅ F) :
    HasStrictlyPerfectModel F := sorry

/-- Complexes with strictly perfect models on a ringed space are closed under isomorphisms. -/
@[stacks 08CM "isomorphism stability of strictly perfect models"]
instance hasStrictlyPerfectModel_isClosedUnderIsomorphisms :
    (SheafOfModules.CochainComplex.hasStrictlyPerfectModel
      (R := X.ringCatSheaf)).IsClosedUnderIsomorphisms where
  of_iso e hE := HasStrictlyPerfectModel.of_iso hE e

/-- Perfect complexes on a ringed space are closed under isomorphisms. -/
@[stacks 08CM "isomorphism stability of perfect complexes"]
instance perfect_isClosedUnderIsomorphisms :
    (SheafOfModules.CochainComplex.perfect (R := X.ringCatSheaf)).IsClosedUnderIsomorphisms where
  of_iso e hE := IsPerfect.of_iso hE e

end AlgebraicGeometry.RingedSpace.CochainComplex
