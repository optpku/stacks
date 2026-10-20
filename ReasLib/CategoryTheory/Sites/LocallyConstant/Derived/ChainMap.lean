module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local chain-map representatives for constant derived sheaves

The pointwise and cover-wise predicates are separated so later arguments can reuse a chosen local
representative without reopening the cover existential.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf.DerivedRestriction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))]
variable [HasDerivedCategory (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, HasDerivedCategory (Sheaf (J.over U) (ModuleCat.{w} Λ))]
variable [∀ U : C, (J.overPullback (ModuleCat.{w} Λ) U).Additive]
variable [∀ U : C, PreservesFiniteLimits (J.overPullback (ModuleCat.{w} Λ) U)]
variable [∀ U : C, PreservesFiniteColimits (J.overPullback (ModuleCat.{w} Λ) U)]

/-- Apply the constant-sheaf functor degreewise to a cochain complex of modules. -/
abbrev constantComplex :
    CochainComplex (ModuleCat.{w} Λ) ℤ ⥤
      CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ :=
  (constantSheaf J (ModuleCat.{w} Λ)).mapHomologicalComplex (up ℤ)

/-- The derived sheaf object represented by a cochain complex. -/
abbrev ofComplex (L : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) :
    DerivedCategory (Sheaf J (ModuleCat.{w} Λ)) :=
  DerivedCategory.Q.obj L

/-- The derived sheaf object represented by the constant-sheaf complex on `K`. -/
abbrev constantObject (K : CochainComplex (ModuleCat.{w} Λ) ℤ) :
    DerivedCategory (Sheaf J (ModuleCat.{w} Λ)) :=
  ofComplex (constantComplex.obj K)

/-- Restrict a cochain complex of sheaves to the slice site over `U`. -/
abbrev restrictComplex
    (L : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) (U : C) :
    CochainComplex (Sheaf (J.over U) (ModuleCat.{w} Λ)) ℤ :=
  ((J.overPullback (ModuleCat.{w} Λ) U).mapHomologicalComplex (up ℤ)).obj L

/-- Restrict the constant-sheaf complex on `K` to the slice site over `U`. -/
abbrev restrictConstantComplex
    (K : CochainComplex (ModuleCat.{w} Λ) ℤ) (U : C) :
    CochainComplex (Sheaf (J.over U) (ModuleCat.{w} Λ)) ℤ :=
  restrictComplex (constantComplex.obj K) U

/-- A derived morphism from a constant complex is represented on `U` when its restriction comes
from an actual chain map through the canonical derived comparison square. -/
@[stacks 09BD "chain-map representation on one slice"]
def IsRepresentedOn
    (K : CochainComplex (ModuleCat.{w} Λ) ℤ)
    (L : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
    (φ : constantObject K ⟶ ofComplex L) (U : C) : Prop :=
  ∃ f : restrictConstantComplex K U ⟶ restrictComplex L U,
    CommSq
      (((J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategory).map φ)
      (((J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategoryFactors.app
        (constantComplex.obj K)).hom)
      (((J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategoryFactors.app L).hom)
      (DerivedCategory.Q.map f)

/-- A derived morphism from a constant complex is locally represented at `X` when it is
represented on every member of some cover of `X`. -/
@[stacks 09BD "cover-wise chain-map representation"]
def IsLocallyRepresentedAt
    (K : CochainComplex (ModuleCat.{w} Λ) ℤ)
    (L : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
    (φ : constantObject K ⟶ ofComplex L) (X : C) : Prop :=
  ∃ T : J.Cover X, ∀ I : T.Arrow, IsRepresentedOn K L φ I.Y

/-- Witness form of `IsRepresentedOn`. -/
theorem isRepresentedOn_iff
    (K : CochainComplex (ModuleCat.{w} Λ) ℤ)
    (L : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
    (φ : constantObject K ⟶ ofComplex L) (U : C) :
    IsRepresentedOn K L φ U ↔
      ∃ f : restrictConstantComplex K U ⟶ restrictComplex L U,
        CommSq
          (((J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategory).map φ)
          (((J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategoryFactors.app
            (constantComplex.obj K)).hom)
          (((J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategoryFactors.app L).hom)
          (DerivedCategory.Q.map f) := sorry

/-- Witness form of `IsLocallyRepresentedAt`. -/
theorem isLocallyRepresentedAt_iff
    (K : CochainComplex (ModuleCat.{w} Λ) ℤ)
    (L : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
    (φ : constantObject K ⟶ ofComplex L) (X : C) :
    IsLocallyRepresentedAt K L φ X ↔
      ∃ T : J.Cover X, ∀ I : T.Arrow, IsRepresentedOn K L φ I.Y := sorry

/-- A derived morphism from the constant sheaf on a bounded complex of finite projective modules
is locally represented by chain maps over any object of the site. -/
@[stacks 09BD "over an arbitrary object"]
theorem locallyRepresentedAt_of_isBoundedFiniteProjective
    (X : C) (K : CochainComplex (ModuleCat.{w} Λ) ℤ) [K.IsBoundedFiniteProjective]
    (L : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
    (φ : constantObject K ⟶ ofComplex L) :
    IsLocallyRepresentedAt K L φ X := sorry

/-- Lemma 21.53.2 (09BD): over a terminal object, a derived morphism from the constant sheaf on
a bounded complex of finite projective modules is locally represented by chain maps. -/
@[stacks 09BD]
theorem locallyRepresentedAt_terminal_of_isBoundedFiniteProjective
    (X : C) (hX : IsTerminal X)
    (K : CochainComplex (ModuleCat.{w} Λ) ℤ) [K.IsBoundedFiniteProjective]
    (L : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
    (φ : constantObject K ⟶ ofComplex L) :
    IsLocallyRepresentedAt K L φ X := sorry

end CategoryTheory.Sheaf.DerivedRestriction
