/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.ZMod.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Absolute
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ConstantPullback

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Finite.ArithmeticFrobenius
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Abelian
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.PullbackIso
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Geometric
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Frobenius.FiniteField

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Absolute Frobenius acts as the identity on constant `ZMod n` small-étale cohomology. -/
theorem absoluteFrobenius_etaleHq_constantZMod_eq_id
    {p : ℕ} [Fact p.Prime] (X : Scheme.{u}) [IsCharP X p] (n j : ℕ) :
    etaleHq_constant_pullback (absoluteFrobenius p X)
        (AddCommGrpCat.of (ULift.{u} (ZMod n))) j =
      𝟙 _ := sorry

/-- Pullback by absolute Frobenius fixes every constant `ZMod n` étale cohomology class. -/
theorem absoluteFrobenius_etaleHq_constantZMod_apply
    {p : ℕ} [Fact p.Prime] (X : Scheme.{u}) [IsCharP X p] (n j : ℕ)
    (ξ : (Sheaf.functorH X.smallEtaleTopology j).obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod n))))) :
    etaleHq_constant_pullback (absoluteFrobenius p X)
        (AddCommGrpCat.of (ULift.{u} (ZMod n))) j ξ =
      ξ := sorry

end AlgebraicGeometry.Scheme

open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- The geometric fibre `X_k̄` has characteristic `p`. -/
instance instIsCharP_geometricFibre (X : SchemeOverField k) :
    Scheme.IsCharP (FieldExtension.baseChange k (AlgebraicClosure k) X.hom) p :=
  isCharP_of_target (FieldExtension.toBase k (AlgebraicClosure k) X.hom)

/-- Geometric Frobenius of `X` after base change to `AlgebraicClosure k`, as
`(π_X)_{k̄}`. -/
def geometricFrobeniusBaseChange (X : SchemeOverField k) :
    FieldExtension.baseChange k (AlgebraicClosure k) X.hom ⟶
      FieldExtension.baseChange k (AlgebraicClosure k) X.hom :=
  ((FieldExtension.Over.functor k (AlgebraicClosure k)).map
      (geometricFrobeniusOver_ofFiniteField X)).left

/-- The base-changed geometric Frobenius lies over `X`. -/
theorem geometricFrobeniusBaseChange_comp_toSource (X : SchemeOverField k) :
    geometricFrobeniusBaseChange X ≫
        FieldExtension.toSource k (AlgebraicClosure k) X.hom =
      FieldExtension.toSource k (AlgebraicClosure k) X.hom ≫
        geometricFrobenius_ofFiniteField X :=
  sorry

/-- Two-step identification `((π_X)_{k̄})^{-1}(F|_{X_k̄}) ≅ (π_X^{-1} F)|_{X_k̄} ≅
F|_{X_k̄}`. -/
def geometricFrobeniusRestrictionIso (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback (geometricFrobeniusBaseChange X)).obj
      (geometricAbelianSheafRestriction X F) ≅ geometricAbelianSheafRestriction X F :=
  (etaleAbelianSheafPullback_comp
        (FieldExtension.toSource k (AlgebraicClosure k) X.hom)
        (geometricFrobeniusBaseChange X)).app F ≪≫
    (eqToIso (congrArg (fun r ↦ etaleAbelianSheafPullback r)
        (geometricFrobeniusBaseChange_comp_toSource X))).app F ≪≫
      (etaleAbelianSheafPullback_comp (geometricFrobenius_ofFiniteField X)
            (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).symm.app F ≪≫
        (etaleAbelianSheafPullback
            (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).mapIso
          ((geometricFrobeniusSheafIso X).app F)

/-- Geometric Frobenius pullback `π_X^*` on `H^j(X_k̄, F|_{X_k̄})`. -/
def geometricFrobeniusEtaleHq (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ) :
    geometricEtaleHq X F j ⟶ geometricEtaleHq X F j :=
  etaleHq_pullback (geometricFrobeniusBaseChange X) (geometricAbelianSheafRestriction X F) j ≫
    (Sheaf.functorH
        (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology
        j).map
      (geometricFrobeniusRestrictionIso X F).hom

/-- Unfolding of `geometricFrobeniusEtaleHq` as pullback along `(π_X)_{k̄}`
followed by the two-step coefficient identification
`((π_X)_{k̄})^{-1}(F|_{X_k̄}) ≅ F|_{X_k̄}`. -/
theorem geometricFrobeniusEtaleHq_spec (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ) :
    geometricFrobeniusEtaleHq X F j =
      etaleHq_pullback (geometricFrobeniusBaseChange X)
          (geometricAbelianSheafRestriction X F) j ≫
        (Sheaf.functorH
            (FieldExtension.baseChange k (AlgebraicClosure k)
              X.hom).smallEtaleTopology
            j).map
          (geometricFrobeniusRestrictionIso X F).hom :=
  rfl

/-- The `f`-fold absolute Frobenius of the geometric fibre equals the composite
of `Spec(FiniteField.arithmeticFrobenius k)` with `(π_X)_{k̄}`. -/
theorem geometricFibre_absoluteFrobeniusPow_eq_galois_comp_geometricFrobenius
    (X : SchemeOverField k) :
    Hom.absoluteFrobeniusPowSource (p := p)
        (FieldExtension.toBase k (AlgebraicClosure k) X.hom)
        (finiteFieldRank k p) =
      FieldExtension.Galois.map k (AlgebraicClosure k) X.hom
          (FiniteField.arithmeticFrobenius k) ≫
        geometricFrobeniusBaseChange X :=
  sorry

/-- Absolute Frobenius of the geometric fibre commutes with geometric Frobenius
in the sense that the two composites with `Spec(FiniteField.arithmeticFrobenius k)`
agree. -/
theorem geometricFibre_absoluteFrobeniusPow_comm_geometricFrobenius
    (X : SchemeOverField k) :
    FieldExtension.Galois.map k (AlgebraicClosure k) X.hom
          (FiniteField.arithmeticFrobenius k) ≫
        geometricFrobeniusBaseChange X =
      geometricFrobeniusBaseChange X ≫
        FieldExtension.Galois.map k (AlgebraicClosure k) X.hom
          (FiniteField.arithmeticFrobenius k) :=
  sorry

/-- Geometric Frobenius pullback `π_X^*` is an isomorphism of geometric étale
cohomology, with inverse the Galois action of arithmetic Frobenius. -/
instance instIsIso_geometricFrobeniusEtaleHq (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ) :
    IsIso (geometricFrobeniusEtaleHq X F j) :=
  ⟨galoisEtaleHq X F j (FiniteField.arithmeticFrobenius k), sorry⟩

/-- Let `F` be an abelian sheaf on `X.smallEtaleTopology`. Then
for all `j : ℕ`, arithmetic Frobenius `(FiniteField.arithmeticFrobenius k)` acts on
`geometricEtaleHq X F j` as the inverse of `geometricFrobeniusEtaleHq X F j`. -/
@[stacks 03SV]
theorem arithmeticFrobenius_etaleHq_eq_inv_geometricFrobenius
    (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ) :
    galoisEtaleHq X F j (FiniteField.arithmeticFrobenius k) =
      CategoryTheory.inv (geometricFrobeniusEtaleHq X F j) :=
  sorry

end AlgebraicGeometry.SchemeOverField
