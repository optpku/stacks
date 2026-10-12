/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.IteratedRelative.Basic
public import stacks_project.Chap59.Lemma_59_91_6_BaseChange
public import stacks_project.Chap64.«64_2_0_1_GeometricFrobenius»
public import stacks_project.Chap64.Lemma_64_3_2_Pullback
public import stacks_project.Chap64.Theorem_64_3_9_GeometricCohomology

/-!
# Geometric Frobenius pullback on ordinary étale cohomology

This leaf owns `(π_X)_{k̄}`, the small-étale site isomorphism for `π_X`, the
coefficient identification `π_X^{-1} F ≅ F`, and the induced endomorphism
`π_X^*` of `H^j(X_k̄, F|_{X_k̄})`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {p : ℕ} [Fact p.Prime]
variable {U X : Scheme.{u}} (f : U ⟶ X)
variable [Scheme.IsCharP X p]

/-- The structure morphism of a Frobenius-power twist of an étale morphism is
étale. -/
instance pPowerTwist_etale [Etale f] (n : ℕ) :
    Etale (pPowerTwist (p := p) f n).hom :=
  inferInstanceAs (Etale (pullback.snd f (absoluteFrobeniusPow p X n)))

/-- Relative Frobenius of a Frobenius-power twist of an étale morphism is an
isomorphism. -/
instance relativeFrobenius_pPowerTwist_isIso [Etale f] (n : ℕ) :
    IsIso (Hom.relativeFrobenius (p := p) (pPowerTwist (p := p) f n).hom) :=
  Hom.relativeFrobenius_isIso_of_etale (pPowerTwist (p := p) f n).hom

/-- Inverse of the underlying scheme morphism of iterated relative Frobenius of
an étale morphism, obtained by reversing successive relative-Frobenius steps. -/
def iteratedRelativeFrobeniusLeftInv [Etale f] :
    (n : ℕ) → (pPowerTwist (p := p) f n).left ⟶ U
  | 0 => pullback.fst f (absoluteFrobeniusPow p X 0)
  | n + 1 =>
      (pPowerTwistSuccIso (p := p) f n).inv.left ≫
        (pullback.congrHom rfl
            (absoluteFrobenius_eq_absoluteFrobeniusPow_one p X)).inv ≫
          CategoryTheory.inv
              (Hom.relativeFrobenius (p := p) (pPowerTwist (p := p) f n).hom) ≫
            iteratedRelativeFrobeniusLeftInv n

/-- The underlying scheme morphism of iterated relative Frobenius of an étale
morphism, as a scheme isomorphism. -/
def iteratedRelativeFrobeniusLeftIso [Etale f] (n : ℕ) :
    U ≅ (pPowerTwist (p := p) f n).left where
  hom := (iteratedRelativeFrobenius (p := p) f n).left
  inv := iteratedRelativeFrobeniusLeftInv (p := p) f n
  hom_inv_id := sorry
  inv_hom_id := sorry

end AlgebraicGeometry.Scheme

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

/-- Geometric Frobenius of `X / k` agrees with the `finiteFieldRank`-fold absolute
Frobenius of the underlying scheme. -/
theorem geometricFrobenius_ofFiniteField_eq_absoluteFrobeniusPow
    (X : SchemeOverField k) :
    geometricFrobenius_ofFiniteField X =
      absoluteFrobeniusPow p X.left (finiteFieldRank k p) :=
  sorry

/-- The small-étale site isomorphism `U ≅ U ×_{π_X} X` induced by iterated
relative Frobenius of an étale morphism `U ⟶ X`. -/
def geometricFrobenius_smallEtalePullbackIso (X : SchemeOverField k) :
    𝟭 X.left.Etale ≅ smallEtalePullback (geometricFrobenius_ofFiniteField X) :=
  NatIso.ofComponents
    (fun U ↦
      -- Local instance justification (search instability): `U.hom` has target `X.left`, but instance search sees the Over-comma `fromPUnit` unfolding.
      letI : Scheme.IsCharP ((Functor.fromPUnit (Over.left X)).obj U.right) p :=
        instIsCharP X
      -- Local instance justification (search instability): `U.prop` is `Etale U.hom`, but the étale-site instance does not fire on `X.left.Etale` objects.
      letI : Etale U.hom := U.prop
      MorphismProperty.Over.isoMk
        (iteratedRelativeFrobeniusLeftIso (p := p) U.hom (finiteFieldRank k p))
        sorry)
    (fun {_ _} _ ↦ sorry)

/-- Canonical identification `π_X^{-1} F ≅ F` of abelian sheaves on `X`, induced
by the small-étale site isomorphism of geometric Frobenius. -/
def geometricFrobeniusSheafIso (X : SchemeOverField k) :
    etaleAbelianSheafPullback (geometricFrobenius_ofFiniteField X) ≅
      𝟭 (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :=
  etaleAbelianSheafPullbackIso (geometricFrobenius_smallEtalePullbackIso X)

/-- The component of `geometricFrobeniusSheafIso` at an abelian sheaf. -/
def geometricFrobeniusSheafIso_hom_app (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback (geometricFrobenius_ofFiniteField X)).obj F ⟶ F :=
  (geometricFrobeniusSheafIso X).hom.app F

/-- Two-step identification `((π_X)_{k̄})^{-1}(F|_{X_k̄}) ≅ (π_X^{-1} F)|_{X_k̄} ≅
F|_{X_k̄}`. -/
def geometricFrobeniusRestrictionIso (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback (geometricFrobeniusBaseChange X)).obj
      (geometricRestriction X F) ≅ geometricRestriction X F :=
  (etaleAbelianSheafPullback_comp
        (FieldExtension.toSource k (AlgebraicClosure k) X.hom)
        (geometricFrobeniusBaseChange X)).app F ≪≫
    (etaleAbelianSheafPullback_congr
        (geometricFrobeniusBaseChange_comp_toSource X)).app F ≪≫
      (etaleAbelianSheafPullback_comp (geometricFrobenius_ofFiniteField X)
            (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).symm.app F ≪≫
        (etaleAbelianSheafPullback
            (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).mapIso
          ((geometricFrobeniusSheafIso X).app F)

/-- Geometric Frobenius pullback `π_X^*` on `H^j(X_k̄, F|_{X_k̄})`. -/
def geometricFrobeniusEtaleHq (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ) :
    geometricEtaleHq X F j ⟶ geometricEtaleHq X F j :=
  etaleHq_pullback (geometricFrobeniusBaseChange X) (geometricRestriction X F) j ≫
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
          (geometricRestriction X F) j ≫
        (Sheaf.functorH
            (FieldExtension.baseChange k (AlgebraicClosure k)
              X.hom).smallEtaleTopology
            j).map
          (geometricFrobeniusRestrictionIso X F).hom :=
  sorry

/-- The `f`-fold absolute Frobenius of the geometric fibre equals the composite
of `Spec(arithmeticFrobeniusEquiv)` with `(π_X)_{k̄}`. -/
theorem geometricFibre_absoluteFrobeniusPow_eq_galois_comp_geometricFrobenius
    (X : SchemeOverField k) :
    Hom.absoluteFrobeniusPowSource (p := p)
        (FieldExtension.toBase k (AlgebraicClosure k) X.hom)
        (finiteFieldRank k p) =
      FieldExtension.Galois.map k (AlgebraicClosure k) X.hom
          arithmeticFrobeniusEquiv ≫
        geometricFrobeniusBaseChange X :=
  sorry

/-- Absolute Frobenius of the geometric fibre commutes with geometric Frobenius
in the sense that the two composites with `Spec(arithmeticFrobeniusEquiv)`
agree. -/
theorem geometricFibre_absoluteFrobeniusPow_comm_geometricFrobenius
    (X : SchemeOverField k) :
    FieldExtension.Galois.map k (AlgebraicClosure k) X.hom
          arithmeticFrobeniusEquiv ≫
        geometricFrobeniusBaseChange X =
      geometricFrobeniusBaseChange X ≫
        FieldExtension.Galois.map k (AlgebraicClosure k) X.hom
          arithmeticFrobeniusEquiv :=
  sorry

end AlgebraicGeometry.SchemeOverField
