/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import stacks_project.Chap67.Lemma_67_13_5_Complement

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

/-- The abelian structure supplies the canonical preadditive structure on étale sheaves. -/
instance etaleSheaf_preadditive {S : Scheme.{u}} (X : AlgebraicSpace S)
    [Abelian (EtaleSheaf X)] : Preadditive (EtaleSheaf X) :=
  (inferInstance : Abelian (EtaleSheaf X)).toPreadditive

/-- Étale sheaves use the zero-morphism instance induced by their preadditive structure. -/
instance etaleSheaf_hasZeroMorphisms {S : Scheme.{u}} (X : AlgebraicSpace S)
    [Abelian (EtaleSheaf X)] : HasZeroMorphisms (EtaleSheaf X) :=
  Preadditive.preadditiveHasZeroMorphisms

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
  sorry

/-- Sheaf-level support on `|Z|` agrees with the geometric-point support condition
`supportSubsetImage` of Morphisms of Spaces, Lemma 67.13.5. -/
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
on the closed image of `i`. This is the source subcategory `D_|Z|(X_étale)`, also written
`D_Z(X_étale)`. -/
abbrev etaleDerivedSupportedOn : ObjectProperty (EtaleDerived X) :=
  DerivedCategory.cohomologyIn (etaleSheafSupportedOn i)

/-- Membership in `etaleDerivedSupportedOn` is the degreewise cohomology-support condition. -/
theorem etaleDerivedSupportedOn_mem_iff (K : EtaleDerived X) :
    etaleDerivedSupportedOn i K ↔
      ∀ n : ℤ, etaleSheafSupportedOn i
        ((DerivedCategory.homologyFunctor (EtaleSheaf X) n).obj K) :=
  sorry

/-- The full subcategory `D_|Z|(X_étale)` of étale derived objects with cohomology
supported on the closed image of `i`. -/
abbrev EtaleDerivedSupported := (etaleDerivedSupportedOn i).FullSubcategory

/-- The inclusion of `D_|Z|(X_étale)` into `D(X_étale)`. -/
abbrev EtaleDerivedSupported.inclusion :
    EtaleDerivedSupported i ⥤ EtaleDerived X :=
  (etaleDerivedSupportedOn i).ι

end AlgebraicGeometry.AlgebraicSpace
