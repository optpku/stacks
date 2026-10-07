module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction.Derived.Basic
public import ReasLib.Algebra.Homology.DifferentialGradedModule.BaseChange.Derived.Basic
public import ReasLib.Algebra.Homology.DifferentialGradedModule.BaseChange.Restriction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Base-Change Restriction Square

This leaf derives the explicit homotopy-level restriction comparison and owns the canonical
commutative square between relative derived tensor and derived restriction of scalars.  It does
not depend on K-flatness or the ordinary derived category of modules.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule.BaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The homotopy source for base change followed by restriction to the coefficient DGA. -/
abbrev restrictedSource (A : CochainDGAlgebra.{u, u} R) :
    CategoryTheory.Functor (K R (DifferentialGradedModule.{u, u} A))
      (DifferentialGradedModule.Derived.Category.{u, u}
        (coefficients (R := R) (S := S))) :=
  restrictedKFunctor (S := S) A ⋙
    DifferentialGradedModule.Derived.Q (coefficients (R := R) (S := S))

/-- The homotopy source for restriction to the ground ring followed by extension to the
coefficient DGA. -/
abbrev extendedSource (A : CochainDGAlgebra.{u, u} R) :
    CategoryTheory.Functor (K R (DifferentialGradedModule.{u, u} A))
      (DifferentialGradedModule.Derived.Category.{u, u}
        (coefficients (R := R) (S := S))) :=
  extendedKFunctor (S := S) A ⋙
    DifferentialGradedModule.Derived.Q (coefficients (R := R) (S := S))

/-- The explicit ordinary restriction comparison, localized in the coefficient derived
category. -/
noncomputable def restrictionSourceIso (A : CochainDGAlgebra.{u, u} R) :
    restrictedSource (S := S) A ≅ extendedSource (S := S) A :=
  Functor.isoWhiskerRight (restrictionComparisonK (S := S) A)
    (DifferentialGradedModule.Derived.Q (coefficients (R := R) (S := S)))

/-- The left-derived ground base-change model followed by canonical derived restriction to the
coefficient DGA. -/
abbrev baseRestrictedDerived (A : CochainDGAlgebra.{u, u} R) :
    CategoryTheory.Functor (DifferentialGradedModule.Derived.Category.{u, u} A)
      (DifferentialGradedModule.Derived.Category.{u, u}
        (coefficients (R := R) (S := S))) :=
  derivedFunctor (S := S) A ⋙
    CochainDGAlgebra.Hom.Derived.restriction (coefficientMap (S := S) A)

/-- Relative derived tensor extension followed by canonical derived restriction to the
coefficient DGA.  This is the top-then-right path in the base-change square. -/
abbrev restrictedDerived (A : CochainDGAlgebra.{u, u} R) :
    CategoryTheory.Functor (DifferentialGradedModule.Derived.Category.{u, u} A)
      (DifferentialGradedModule.Derived.Category.{u, u}
        (coefficients (R := R) (S := S))) :=
  DifferentialGradedBimodule.Tensor.derivedFunctor (extension (S := S) A) ⋙
    CochainDGAlgebra.Hom.Derived.restriction (coefficientMap (S := S) A)

/-- Canonical derived restriction to the ground ring followed by derived extension to the
coefficient DGA. -/
abbrev extendedDerived (A : CochainDGAlgebra.{u, u} R) :
    CategoryTheory.Functor (DifferentialGradedModule.Derived.Category.{u, u} A)
      (DifferentialGradedModule.Derived.Category.{u, u}
        (coefficients (R := R) (S := S))) :=
  CochainDGAlgebra.Hom.Derived.restriction (groundMap A) ⋙
    DifferentialGradedBimodule.Tensor.derivedFunctor
      (coefficientExtension (R := R) (S := S))

/-- The derived-to-underived comparison for the restricted base-change path. -/
noncomputable def restrictedCounit (A : CochainDGAlgebra.{u, u} R) :
    DifferentialGradedModule.Derived.Q A ⋙ baseRestrictedDerived (S := S) A ⟶
      restrictedSource (S := S) A where
  app M :=
    (CochainDGAlgebra.Hom.Derived.restriction
      (coefficientMap (S := S) A)).map ((derivedCounit (S := S) A).app M) ≫
      (CochainDGAlgebra.Hom.Derived.restrictionFac
        (coefficientMap (S := S) A)).hom.app ((dgFunctor (S := S) A).mapK.obj M)
  naturality := sorry

/-- The derived-to-underived comparison for restriction to the ground ring followed by
coefficient extension. -/
noncomputable def extendedCounit (A : CochainDGAlgebra.{u, u} R) :
    DifferentialGradedModule.Derived.Q A ⋙ extendedDerived (S := S) A ⟶
      extendedSource (S := S) A where
  app M :=
    (DifferentialGradedBimodule.Tensor.derivedFunctor
      (coefficientExtension (R := R) (S := S))).map
        ((CochainDGAlgebra.Hom.Derived.restrictionFac (groundMap A)).hom.app M) ≫
      (DifferentialGradedBimodule.Tensor.derivedCounit
        (coefficientExtension (R := R) (S := S))).app
          ((groundMap A).restrictDgFunctor.mapK.obj M)
  naturality := sorry

/-- The restricted base-change path is a left-derived model of its explicit homotopy source. -/
instance baseRestrictedDerived_isLeftDerived (A : CochainDGAlgebra.{u, u} R) :
    (baseRestrictedDerived (S := S) A).IsLeftDerivedFunctor
      (restrictedCounit (S := S) A)
      (DifferentialGradedModule.quasiIso A) := sorry

/-- The restriction-then-extension path is a left-derived model of its explicit homotopy
source. -/
instance extendedDerived_isLeftDerived (A : CochainDGAlgebra.{u, u} R) :
    (extendedDerived (S := S) A).IsLeftDerivedFunctor (extendedCounit (S := S) A)
      (DifferentialGradedModule.quasiIso A) := sorry

/-- The two left-derived models of the ordinary restriction square are canonically
isomorphic. -/
noncomputable def baseRestrictionSquareIso (A : CochainDGAlgebra.{u, u} R) :
    baseRestrictedDerived (S := S) A ≅ extendedDerived (S := S) A :=
  Functor.leftDerivedNatIso
    (baseRestrictedDerived (S := S) A) (extendedDerived (S := S) A)
    (restrictedCounit (S := S) A) (extendedCounit (S := S) A)
    (DifferentialGradedModule.quasiIso A) (restrictionSourceIso (S := S) A)

/-- The left-derived restriction-square comparison is characterized by the explicit ordinary
restriction comparison. -/
theorem baseRestrictionSquareIso_fac (A : CochainDGAlgebra.{u, u} R) :
    Functor.whiskerLeft (DifferentialGradedModule.Derived.Q A)
        (baseRestrictionSquareIso (S := S) A).hom ≫ extendedCounit (S := S) A =
      restrictedCounit (S := S) A ≫ (restrictionSourceIso (S := S) A).hom := sorry

/-- Lemma 22.33.8 (0BYZ) (2): the derived tensor base-change square with the two canonical
restriction-of-scalars functors commutes up to its canonical natural isomorphism. -/
@[stacks 0BYZ "derived restriction-of-scalars base-change square"]
noncomputable def restrictionSquareIso (A : CochainDGAlgebra.{u, u} R) :
    restrictedDerived (S := S) A ≅ extendedDerived (S := S) A :=
  (Functor.isoWhiskerRight (derivedIso (S := S) A).symm
    (CochainDGAlgebra.Hom.Derived.restriction
      (coefficientMap (S := S) A))).trans (baseRestrictionSquareIso (S := S) A)

/-- The public restriction-square isomorphism first identifies relative derived tensor with
derived ground base change and then applies the descended ordinary restriction comparison. -/
theorem restrictionSquareIso_hom (A : CochainDGAlgebra.{u, u} R) :
    (restrictionSquareIso (S := S) A).hom =
      (Functor.isoWhiskerRight (derivedIso (S := S) A).symm
        (CochainDGAlgebra.Hom.Derived.restriction
          (coefficientMap (S := S) A))).hom ≫
        (baseRestrictionSquareIso (S := S) A).hom := sorry

end DifferentialGradedModule.BaseChange
