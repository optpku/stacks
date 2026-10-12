/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Pushout
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Left
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived scalar extension around a pushout square

This file owns the natural comparison between the two derived scalar routes around a pushout
square.  The comparison is constructed from the module-level pushout isomorphism and the
universal property of the total left derived functor.  The tensor-product namespace specializes
the generic construction to the square with target `R' \otimes_R A`.

The facade is universe-aligned: all four rings and the module carriers live in the same universe.
The underlying module-level pushout comparison remains universe-polymorphic.

@stack 065Z
-/

@[expose] public section

noncomputable section

open CategoryTheory ComplexShape
open scoped TensorProduct DerivedTensorWithAlgebra

universe u

namespace CategoryTheory.ModuleCat.Pushout.DerivedExtension

variable {R A R' A' : Type u}
variable [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
variable [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
variable [IsScalarTower R A A'] [IsScalarTower R R' A']
variable [Algebra.IsPushout R R' A A']

/-- The universe-aligned module category used by this convenience facade. -/
@[stacks 065Z "aligned module category for derived pushout base change"]
abbrev AlignedModule (S : Type u) [CommRing S] := ModuleCat.{u, u} S

/-- The standard derived category of an aligned module category. -/
@[stacks 065Z "aligned derived category for pushout base change"]
abbrev AlignedDerived (S : Type u) [CommRing S] :=
  DerivedCategory.{u + 1, u, u + 1} (AlignedModule S)

/-- The homotopy category used to construct the aligned derived comparison. -/
@[stacks 065Z "aligned homotopy category for pushout base change"]
abbrev AlignedHomotopy (S : Type u) [CommRing S] :=
  HomotopyCategory (AlignedModule S) (up ℤ)


/-- Extension along the upper edge `A → A'` of a pushout square. -/
@[stacks 065Z "extension along the target edge of a pushout square"]
abbrev extendTarget : AlignedModule A ⥤ AlignedModule A' :=
  ModuleCat.extendScalars.{u, u, u} (algebraMap A A')

/-- Restriction along the left edge `R → A` of a pushout square. -/
@[stacks 065Z "restriction along the algebra edge of a pushout square"]
abbrev restrictBase : AlignedModule A ⥤ AlignedModule R :=
  ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)

/-- Restriction along the right edge `R' → A'` of a pushout square. -/
@[stacks 065Z "restriction along the target algebra edge of a pushout square"]
abbrev restrictTarget : AlignedModule A' ⥤ AlignedModule R' :=
  ModuleCat.restrictScalars.{u, u, u} (algebraMap R' A')

/-- Extension along the lower edge `R → R'` of a pushout square. -/
@[stacks 065Z "extension along the base edge of a pushout square"]
abbrev extendBase : AlignedModule R ⥤ AlignedModule R' :=
  ModuleCat.extendScalars.{u, u, u} (algebraMap R R')

/-- The derived route through the target algebra `A'`, followed by restriction to `R'`. -/
@[stacks 065Z "derived route through the target algebra in a pushout square"]
abbrev algebraDerived : AlignedDerived A ⥤ AlignedDerived R' :=
  (ModuleCat.derivedExtensionOfScalars.{u, u, u} (algebraMap A A') : AlignedDerived A ⥤ AlignedDerived A') ⋙
    (restrictTarget (R' := R') (A' := A')).mapDerivedCategory

/-- The derived route through the base ring `R`, followed by extension to `R'`. -/
@[stacks 065Z "derived route through the base ring in a pushout square"]
abbrev baseDerived : AlignedDerived A ⥤ AlignedDerived R' :=
  (restrictBase (R := R) (A := A)).mapDerivedCategory ⋙
    (ModuleCat.derivedExtensionOfScalars.{u, u, u} (algebraMap R R') : AlignedDerived R ⥤ AlignedDerived R')

/-- The composite localization counit for the route through `A'`. -/
@[stacks 065Z "localization counit for the target-algebra route"]
noncomputable abbrev algebraCounit :
    (DerivedCategory.Qh : AlignedHomotopy A ⥤ AlignedDerived A) ⋙ (algebraDerived (A := A) (R' := R') (A' := A')) ⟶
      (extendTarget (A := A) (A' := A')).mapHomotopyCategory (up ℤ) ⋙
        (restrictTarget (R' := R') (A' := A')).mapHomotopyCategory (up ℤ) ⋙ (DerivedCategory.Qh : AlignedHomotopy R' ⥤ AlignedDerived R') :=
  @Functor.LeftDerived.Composition.iteratedCounit
    (AlignedHomotopy A) (AlignedHomotopy A') (AlignedDerived R')
    (AlignedDerived A) (AlignedDerived A')
    _ _ _ _ _
    (F := (extendTarget (A := A) (A' := A')).mapHomotopyCategory (up ℤ))
    (G := (restrictTarget (R' := R') (A' := A')).mapHomotopyCategory (up ℤ) ⋙ (DerivedCategory.Qh : AlignedHomotopy R' ⥤ AlignedDerived R'))
    (L := (DerivedCategory.Qh : AlignedHomotopy A ⥤ AlignedDerived A)) (L' := (DerivedCategory.Qh : AlignedHomotopy A' ⥤ AlignedDerived A'))
    (LF := (ModuleCat.derivedExtensionOfScalars.{u, u, u} (algebraMap A A') : AlignedDerived A ⥤ AlignedDerived A'))
    (LG := ((restrictTarget (R' := R') (A' := A')).mapDerivedCategory : AlignedDerived A' ⥤ AlignedDerived R'))
    (ModuleCat.derivedExtensionOfScalarsCounit (algebraMap A A'))
    ((restrictTarget (R' := R') (A' := A')).mapDerivedCategoryFactorsh.hom)

/-- The composite localization counit for the route through `R`. -/
@[stacks 065Z "localization counit for the base-ring route"]
noncomputable abbrev baseCounit :
    (DerivedCategory.Qh : AlignedHomotopy A ⥤ AlignedDerived A) ⋙ (baseDerived (R := R) (A := A) (R' := R')) ⟶
      (restrictBase (R := R) (A := A)).mapHomotopyCategory (up ℤ) ⋙
        (extendBase (R := R) (R' := R')).mapHomotopyCategory (up ℤ) ⋙ (DerivedCategory.Qh : AlignedHomotopy R' ⥤ AlignedDerived R') :=
  @Functor.LeftDerived.Composition.iteratedCounit
    (AlignedHomotopy A) (AlignedHomotopy R) (AlignedDerived R')
    (AlignedDerived A) (AlignedDerived R)
    _ _ _ _ _
    (F := (restrictBase (R := R) (A := A)).mapHomotopyCategory (up ℤ))
    (G := (extendBase (R := R) (R' := R')).mapHomotopyCategory (up ℤ) ⋙ (DerivedCategory.Qh : AlignedHomotopy R' ⥤ AlignedDerived R'))
    (L := (DerivedCategory.Qh : AlignedHomotopy A ⥤ AlignedDerived A)) (L' := (DerivedCategory.Qh : AlignedHomotopy R ⥤ AlignedDerived R))
    (LF := ((restrictBase (R := R) (A := A)).mapDerivedCategory : AlignedDerived A ⥤ AlignedDerived R))
    (LG := (ModuleCat.derivedExtensionOfScalars.{u, u, u} (algebraMap R R') : AlignedDerived R ⥤ AlignedDerived R'))
    ((restrictBase (R := R) (A := A)).mapDerivedCategoryFactorsh.hom)
    (ModuleCat.derivedExtensionOfScalarsCounit (algebraMap R R'))

/-- The route through `A'` is a total left derived functor of its homotopy-level route. -/
@[stacks 065Z "left-derived structure on the target-algebra route"]
instance algebraDerived_isLeftDerived :
    (algebraDerived (A := A) (R' := R') (A' := A')).IsLeftDerivedFunctor
      (algebraCounit (A := A) (R' := R') (A' := A')) (HomotopyCategory.quasiIso (AlignedModule A) (up ℤ)) := sorry

/-- The homotopy-level route through `A'`. -/
@[stacks 065Z "homotopy-level route through the target algebra"]
noncomputable abbrev algebraHomotopy : AlignedHomotopy A ⥤ AlignedDerived R' :=
  (extendTarget (A := A) (A' := A')).mapHomotopyCategory (up ℤ) ⋙
    (restrictTarget (R' := R') (A' := A')).mapHomotopyCategory (up ℤ) ⋙ (DerivedCategory.Qh : AlignedHomotopy R' ⥤ AlignedDerived R')

/-- The homotopy-level route through `R`. -/
@[stacks 065Z "homotopy-level route through the base ring"]
noncomputable abbrev baseHomotopy : AlignedHomotopy A ⥤ AlignedDerived R' :=
  (restrictBase (R := R) (A := A)).mapHomotopyCategory (up ℤ) ⋙
    (extendBase (R := R) (R' := R')).mapHomotopyCategory (up ℤ) ⋙ (DerivedCategory.Qh : AlignedHomotopy R' ⥤ AlignedDerived R')

/-- The module-level pushout isomorphism transported to homotopy categories. -/
@[stacks 065Z "homotopy-level pushout route comparison"]
noncomputable def routeIso :
    algebraHomotopy (A := A) (R' := R') (A' := A') ≅
      baseHomotopy (R := R) (A := A) (R' := R') :=
  let hAlgebra :=
    Functor.mapHomotopyCategoryCompIso
      (F := extendTarget (A := A) (A' := A'))
      (G := restrictTarget (R' := R') (A' := A'))
      (H := ModuleCat.Pushout.fromAlgebra (A := A) (R' := R') (A' := A'))
      (Iso.refl _) (up ℤ)
  let hBase :=
    Functor.mapHomotopyCategoryCompIso
      (F := restrictBase (R := R) (A := A))
      (G := extendBase (R := R) (R' := R'))
      (H := ModuleCat.Pushout.fromBase (R := R) (A := A) (R' := R'))
      (Iso.refl _) (up ℤ)
  Functor.isoWhiskerRight hAlgebra (DerivedCategory.Qh : AlignedHomotopy R' ⥤ AlignedDerived R') ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryIso
        (ModuleCat.Pushout.natIso (R := R) (A := A) (R' := R') (A' := A'))) (DerivedCategory.Qh : AlignedHomotopy R' ⥤ AlignedDerived R') ≪≫
    (Functor.isoWhiskerRight hBase (DerivedCategory.Qh : AlignedHomotopy R' ⥤ AlignedDerived R')).symm

/-- The canonical derived comparison from the base route to the target-algebra route. -/
@[stacks 065Z "derived pushout base-change comparison"]
noncomputable def comparison :
    baseDerived (R := R) (A := A) (R' := R') ⟶
      algebraDerived (A := A) (R' := R') (A' := A') :=
  Functor.leftDerivedNatTrans
    (baseDerived (R := R) (A := A) (R' := R'))
    (algebraDerived (A := A) (R' := R') (A' := A'))
    (baseCounit (R := R) (A := A) (R' := R'))
    (algebraCounit (A := A) (R' := R') (A' := A')) (HomotopyCategory.quasiIso (AlignedModule A) (up ℤ))
    (routeIso (R := R) (A := A) (R' := R') (A' := A')).inv

/-- The component of the canonical derived pushout comparison. -/
@[stacks 065Z "derived pushout base-change comparison at an object"]
noncomputable abbrev comparisonApp (K : AlignedDerived A) :
    (baseDerived (R := R) (A := A) (R' := R')).obj K ⟶
      (algebraDerived (A := A) (R' := R') (A' := A')).obj K :=
  (comparison (R := R) (A := A) (R' := R') (A' := A')).app K

namespace TensorProduct

variable {R A R' : Type u}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

-- Local instance justification (instance diamond): expose both canonical tensor-factor algebra
-- structures only in the tensor-product pushout facade.
attribute [local instance] Algebra.TensorProduct.leftAlgebra Algebra.TensorProduct.rightAlgebra


/-- The base route for the canonical pushout with target `R' ⊗[R] A`. -/
@[stacks 065Z "base route for the tensor-product pushout"]
abbrev baseDerived :
    DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u, u} A) ⥤
      DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u, u} R') :=
  Pushout.DerivedExtension.baseDerived
    (R := R) (A := A) (R' := R')

/-- The target-algebra route for the canonical pushout with target `R' ⊗[R] A`. -/
@[stacks 065Z "target-algebra route for the tensor-product pushout"]
abbrev algebraDerived :
    DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u, u} A) ⥤
      DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u, u} R') :=
  Pushout.DerivedExtension.algebraDerived
    (A := A) (R' := R') (A' := (R' ⊗[R] A))

/-- The canonical derived comparison for the tensor-product pushout `R' ⊗[R] A`. -/
@[stacks 065Z "tensor-product derived base-change comparison"]
noncomputable abbrev comparison :
    baseDerived (R := R) (A := A) (R' := R') ⟶
      algebraDerived (R := R) (A := A) (R' := R') :=
  Pushout.DerivedExtension.comparison
    (R := R) (A := A) (R' := R') (A' := (R' ⊗[R] A))

/-- The objectwise tensor-product derived base-change comparison. -/
@[stacks 065Z "tensor-product derived base-change comparison at an object"]
noncomputable abbrev comparisonApp
    (K : DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u, u} A)) :
    (baseDerived (R := R) (A := A) (R' := R')).obj K ⟶
      (algebraDerived (R := R) (A := A) (R' := R')).obj K :=
  (comparison (R := R) (A := A) (R' := R')).app K

end TensorProduct

end CategoryTheory.ModuleCat.Pushout.DerivedExtension
