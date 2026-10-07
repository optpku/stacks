module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import stacks_project.Chap61.Lemma_61_19_1_Comparison

/-!
# Derived étale-to-pro-étale adjunction

The bounded-below derived adjunction `ε⁻¹ ⊣ Rε_*` induced by `etaleToProEt`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The bounded-below right-derived functor of abelian `ε_*` exists. -/
instance etaleToProEtSheaf_hasRightDerivedFunctor (X : Scheme.{u}) :
    (etaleToProEtSheaf X AddCommGrpCat.{u + 1}).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1})) :=
  sorry

/-- Bounded-below derived direct image `Rε_*` on `D⁺`. -/
def etaleToProEt_plusPushforward (X : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.Plus.right (etaleToProEtSheaf X AddCommGrpCat.{u + 1})

/-- Derived direct image `Rε_*` is the bounded-below right-derived functor of abelian
`etaleToProEtSheaf`. -/
theorem etaleToProEt_plusPushforward_eq (X : Scheme.{u}) :
    etaleToProEt_plusPushforward X =
      Adjunction.Derived.Plus.right (etaleToProEtSheaf X AddCommGrpCat.{u + 1}) :=
  sorry

variable (X : Scheme.{u})
variable [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (etaleToProEt X).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}]

/-- The sheaf-level adjunction unit of abelian `ε⁻¹ ⊣ ε_*` is an isomorphism. -/
theorem etaleToProEt_sheafAdjunction_addCommGrp_unit_app_isIso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((etaleToProEt_sheafAdjunction X AddCommGrpCat.{u + 1}).unit.app F) :=
  sorry

/-- Higher direct images `R^q ε_* (ε⁻¹ I)` vanish for injective abelian sheaves and `0 < q`. -/
theorem etaleToProEtSheaf_rightDerived_pullback_isZero
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective I]
    (q : ℕ) (hq : 0 < q) :
    IsZero
      (((etaleToProEtSheaf X AddCommGrpCat.{u + 1}).rightDerived q).obj
        ((etaleToProEtPullback X AddCommGrpCat.{u + 1}).obj I)) :=
  sorry

variable [PreservesFiniteLimits (etaleToProEtPullback X AddCommGrpCat.{u + 1})]
variable [PreservesFiniteColimits (etaleToProEtPullback X AddCommGrpCat.{u + 1})]

/-- Bounded-below derived inverse image `ε⁻¹` on `D⁺`. -/
def etaleToProEt_plusPullback :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.Plus.left
    (ExactFunctor.of (etaleToProEtPullback X AddCommGrpCat.{u + 1}))

/-- Derived inverse image `ε⁻¹` is the exact-left bounded-below derived functor of abelian
`etaleToProEtPullback`. -/
theorem etaleToProEt_plusPullback_eq :
    etaleToProEt_plusPullback X =
      Adjunction.Derived.Plus.left
        (ExactFunctor.of (etaleToProEtPullback X AddCommGrpCat.{u + 1})) :=
  sorry

/-- Bounded-below derived adjunction `ε⁻¹ ⊣ Rε_*` on `D⁺`. -/
def etaleToProEt_plusAdjunction :
    etaleToProEt_plusPullback X ⊣ etaleToProEt_plusPushforward X :=
  Adjunction.Derived.Plus.adjunction
    (ExactFunctor.of (etaleToProEtPullback X AddCommGrpCat.{u + 1}))
    (etaleToProEtSheaf X AddCommGrpCat.{u + 1})
    (etaleToProEt_sheafAdjunction X AddCommGrpCat.{u + 1})

/-- The `D⁺` adjunction `ε⁻¹ ⊣ Rε_*` is the exact-left bounded-below derived adjunction of
abelian `ε⁻¹ ⊣ ε_*`. -/
theorem etaleToProEt_plusAdjunction_eq :
    etaleToProEt_plusAdjunction X =
      Adjunction.Derived.Plus.adjunction
        (ExactFunctor.of (etaleToProEtPullback X AddCommGrpCat.{u + 1}))
        (etaleToProEtSheaf X AddCommGrpCat.{u + 1})
        (etaleToProEt_sheafAdjunction X AddCommGrpCat.{u + 1}) :=
  sorry

/-- The canonical derived unit `K ⟶ Rε_* ε⁻¹ K`. -/
def etaleToProEt_derivedUnit
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    K ⟶ (etaleToProEt_plusPushforward X).obj ((etaleToProEt_plusPullback X).obj K) :=
  (etaleToProEt_plusAdjunction X).unit.app K

/-- `etaleToProEt_derivedUnit` is the unit of `etaleToProEt_plusAdjunction`. -/
theorem etaleToProEt_derivedUnit_eq
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    etaleToProEt_derivedUnit X K = (etaleToProEt_plusAdjunction X).unit.app K :=
  sorry

end AlgebraicGeometry.Scheme

end

end
