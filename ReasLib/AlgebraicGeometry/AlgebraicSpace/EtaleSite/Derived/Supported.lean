module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.ClosedImmersion
public import ReasLib.CategoryTheory.Functor.Derived.Model

/-!
# Étale derived categories of algebraic spaces with support on a closed subspace

Abelian sheaves and derived categories on the small étale site of an algebraic space,
together with the strictly full subcategory `D_|Z|(X_étale)` of objects whose
cohomology sheaves are supported on the closed image of a closed immersion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Abelian sheaves on the small étale site of an algebraic space. -/
abbrev EtaleSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}

-- Local instance justification (defeq pin): sheaf preadditive inference otherwise differs from the Abelian-induced structures fixed by DerivedCategory.Qh and exact-derived factorization; pin the existing canonical projections consistently for homotopy categories, additive binders, and derived models.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- The homotopy category of cochain complexes of abelian étale sheaves on an algebraic space. -/
abbrev EtaleHomotopy {S : Scheme.{u}} (X : AlgebraicSpace S) [Abelian (EtaleSheaf X)]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}] :=
  HomotopyCategory (EtaleSheaf X) (ComplexShape.up ℤ)

/-- The derived category `D(X_étale)` of abelian étale sheaves on an algebraic space. -/
abbrev EtaleDerived {S : Scheme.{u}} (X : AlgebraicSpace S) [Abelian (EtaleSheaf X)]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasDerivedCategory (EtaleSheaf X)] :=
  DerivedCategory (EtaleSheaf X)

/-- Quasi-isomorphisms in the homotopy category of abelian étale sheaves on an algebraic space. -/
abbrev etaleQuasiIso {S : Scheme.{u}} (X : AlgebraicSpace S) [Abelian (EtaleSheaf X)]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}] :=
  HomotopyCategory.quasiIso (EtaleSheaf X) (ComplexShape.up ℤ)

/-- The localization from the étale homotopy category to the étale derived category. -/
abbrev etaleDerivedQuotient {S : Scheme.{u}} (X : AlgebraicSpace S) [Abelian (EtaleSheaf X)]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasDerivedCategory (EtaleSheaf X)] :
    EtaleHomotopy X ⥤ EtaleDerived X :=
  (DerivedCategory.Qh : EtaleHomotopy X ⥤ EtaleDerived X)

variable {S : Scheme.{u}}

/-- An explicit total right-derived model of an additive functor between categories of
abelian étale sheaves on algebraic spaces. -/
abbrev EtaleRightDerivedModel {X Y : AlgebraicSpace S}
    [Abelian (EtaleSheaf X)] [Abelian (EtaleSheaf Y)]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasDerivedCategory (EtaleSheaf X)] [HasDerivedCategory (EtaleSheaf Y)]
    (F : EtaleSheaf X ⥤ EtaleSheaf Y) [F.Additive] :=
  CategoryTheory.Functor.RightDerived.Model
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ etaleDerivedQuotient Y)
    (etaleDerivedQuotient X) (etaleQuasiIso X)

variable {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
variable [Etale (closedImmersionComplementι i)]
variable [Abelian (EtaleSheaf X)]
variable [Abelian (EtaleSheaf (closedImmersionComplement i))]
variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasDerivedCategory (EtaleSheaf X)]

/-- An abelian étale sheaf on `X` is supported on the closed image of `i` when its
restriction along the open complement `X \ Z` is a zero object. -/
abbrev etaleSheafSupportedOn : ObjectProperty (EtaleSheaf X) :=
  fun F ↦ IsZero
    ((etaleRestrictionSheaf (closedImmersionComplementι i) AddCommGrpCat.{u + 1}).obj F)

/-- Membership in `etaleSheafSupportedOn` is exactly vanishing of restriction to the
open complement of `i`. -/
theorem etaleSheafSupportedOn_iff (F : EtaleSheaf X) :
    etaleSheafSupportedOn i F ↔
      IsZero
        ((etaleRestrictionSheaf (closedImmersionComplementι i) AddCommGrpCat.{u + 1}).obj F) :=
  Iff.rfl

/-- Sheaf-level support on `|Z|` agrees with the geometric-point support condition
`supportSubsetImage`. -/
theorem etaleSheafSupportedOn_iff_supportSubsetImage
    [∀ (xbar : GeometricPoint X) (G : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (etaleBaseChange xbar.hom).op.HasLeftKanExtension G]
    [∀ xbar : GeometricPoint X,
      HasWeakSheafify (spacesEtaleTopology (ofOver xbar.toFieldValuedPoint.overObj))
        AddCommGrpCat.{u + 1}]
    (F : EtaleSheaf X) :
    etaleSheafSupportedOn i F ↔ supportSubsetImage i F :=
  sorry

/-- Support on the closed image of `i` is closed under isomorphisms of abelian étale sheaves. -/
instance etaleSheafSupportedOn.instIsClosedUnderIsomorphisms :
    (etaleSheafSupportedOn i).IsClosedUnderIsomorphisms :=
  sorry

/-- The zero sheaf is supported on the closed image of `i`. -/
instance etaleSheafSupportedOn.instContainsZero :
    (etaleSheafSupportedOn i).ContainsZero :=
  sorry

/-- The object property of étale derived objects whose cohomology sheaves are supported
on the closed image of `i`. -/
abbrev etaleDerivedSupportedOn : ObjectProperty (EtaleDerived X) :=
  DerivedCategory.cohomologyIn (etaleSheafSupportedOn i)

/-- Membership in `etaleDerivedSupportedOn` is the degreewise cohomology-support condition. -/
theorem etaleDerivedSupportedOn_mem_iff (K : EtaleDerived X) :
    etaleDerivedSupportedOn i K ↔
      ∀ n : ℤ, etaleSheafSupportedOn i
        ((DerivedCategory.homologyFunctor (EtaleSheaf X) n).obj K) :=
  Iff.rfl

/-- The full subcategory `D_|Z|(X_étale)` of étale derived objects with cohomology
supported on the closed image of `i`. -/
abbrev EtaleDerivedSupported := (etaleDerivedSupportedOn i).FullSubcategory

/-- The inclusion of `D_|Z|(X_étale)` into `D(X_étale)`. -/
abbrev EtaleDerivedSupported.inclusion :
    EtaleDerivedSupported i ⥤ EtaleDerived X :=
  (etaleDerivedSupportedOn i).ι

end AlgebraicGeometry.AlgebraicSpace
