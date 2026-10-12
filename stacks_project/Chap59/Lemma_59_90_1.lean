/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_91_12_BaseChange
public import stacks_project.Chap59.Theorem_59_89_2_Smooth_base_change
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe w u

namespace AlgebraicGeometry.FieldExtension

/-- The base change of `g : T ⟶ S` along `Spec L ⟶ Spec K`, as a morphism
`T_L ⟶ S_L` of field-extension pullbacks. -/
abbrev baseChangeHom (K L : Type u) [Field K] [Field L] [Algebra K L]
    {T S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (g : T ⟶ S) :
    baseChange K L (g ≫ s) ⟶ baseChange K L s :=
  ((Over.functor K L).map
    (CategoryTheory.Over.homMk g rfl :
      CategoryTheory.Over.mk (g ≫ s) ⟶ CategoryTheory.Over.mk s)).left

/-- `baseChangeHom` is the underlying scheme morphism of the image of `g` under
`FieldExtension.Over.functor`. -/
theorem baseChangeHom_eq (K L : Type u) [Field K] [Field L] [Algebra K L]
    {T S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (g : T ⟶ S) :
    baseChangeHom K L s g =
      ((Over.functor K L).map
        (CategoryTheory.Over.homMk g rfl :
          CategoryTheory.Over.mk (g ≫ s) ⟶ CategoryTheory.Over.mk s)).left := sorry

/-- The field-extension base change of `g` commutes with projection to the source
schemes. -/
theorem baseChangeHom_toSource (K L : Type u) [Field K] [Field L] [Algebra K L]
    {T S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (g : T ⟶ S) :
    baseChangeHom K L s g ≫ toSource K L s = toSource K L (g ≫ s) ≫ g := sorry

/-- The field-extension base change of `g` commutes with projection to `Spec L`. -/
theorem baseChangeHom_toBase (K L : Type u) [Field K] [Field L] [Algebra K L]
    {T S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (g : T ⟶ S) :
    baseChangeHom K L s g ≫ toBase K L s = toBase K L (g ≫ s) := sorry

/-- The commutative square of `g` and its field-extension base change is cartesian. -/
theorem baseChangeHom_isPullback (K L : Type u) [Field K] [Field L] [Algebra K L]
    {T S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (g : T ⟶ S) :
    IsPullback (toSource K L (g ≫ s)) (baseChangeHom K L s g) g (toSource K L s) :=
  (IsPullback.of_right
      ((baseChangeHom_toBase K L s g).symm ▸
        (IsPullback.of_hasPullback (g ≫ s) (specMap K L)).flip)
      (baseChangeHom_toSource K L s g)
      (IsPullback.of_hasPullback s (specMap K L)).flip).flip

end AlgebraicGeometry.FieldExtension

namespace AlgebraicGeometry.Scheme.Hom

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- Lemma 59.90.1: if `L / K` is an extension of fields and `g : T ⟶ S` is a
quasi-compact and quasi-separated morphism of schemes over `Spec K`, then for
every `E ∈ D⁺(T_étale)` whose cohomology sheaves have geometric stalks that are
torsion of orders invertible in `K`, the canonical derived base-change map
identifies `R(g_L)_* E_L` with the pullback of `Rg_* E` to `S_L`. Here
`S_L = FieldExtension.baseChange K L s`,
`T_L = FieldExtension.baseChange K L (g ≫ s)`,
`g_L = FieldExtension.baseChangeHom K L s g`, and
`E_L = (etaleDerivedInverseImage (FieldExtension.toSource K L (g ≫ s))).obj E`. -/
@[stacks 0F1C]
theorem derivedBaseChange_isIso_of_fieldExtension
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {T S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g]
    [(abelianPushforwardAlong g).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong (FieldExtension.baseChangeHom K L s g)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (FieldExtension.baseChange K L (g ≫ s)).smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact (FieldExtension.toSource K L s)).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etalePullbackExact (FieldExtension.toSource K L (g ≫ s))).obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}))]
    [(abelianPushforwardAlong g ⋙
        (etalePullbackExact (FieldExtension.toSource K L s)).obj).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}))]
    [((etalePullbackExact (FieldExtension.toSource K L (g ≫ s))).obj ⋙
        abelianPushforwardAlong (FieldExtension.baseChangeHom K L s g)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}))]
    (h_src : IsIso (derivedSourceComparison g (FieldExtension.toSource K L s)))
    (E : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsTorsionWithOrdersInvertibleOn (Spec (CommRingCat.of K)) :
        ObjectProperty (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})) E) :
    IsIso (derivedBaseChangeHom g (FieldExtension.toSource K L s)
      (FieldExtension.baseChangeHom K L s g)
      (FieldExtension.toSource K L (g ≫ s))
      (FieldExtension.baseChangeHom_isPullback K L s g) h_src E) := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
