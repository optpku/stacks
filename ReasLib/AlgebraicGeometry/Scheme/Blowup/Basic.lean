/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
import Mathlib.Tactic.CrossRefAttribute

/-!
# Blowups and admissible blowups

This file packages the universal property of a blowup in an ideal sheaf and defines blowups whose
centers are finitely presented and disjoint from a chosen open subscheme.
-/

@[expose] public section

namespace AlgebraicGeometry

universe u

open CategoryTheory
open Scheme.IdealSheafData

section

variable {X X' : Scheme.{u}} {I : X.IdealSheafData}

/-- A morphism `f : X' ⟶ X` is a blowup of `X` in the closed subscheme defined by `I` when the
inverse-image center is an effective Cartier divisor and `f` is terminal among morphisms to `X`
with that property. -/
@[stacks 0806 "blowup universal property"]
class IsBlowup (f : X' ⟶ X) (I : X.IdealSheafData) : Prop where
  /-- The inverse-image center on the blowup is an effective Cartier divisor. -/
  toIsEffectiveCartierDivisor :
    AlgebraicGeometry.IsEffectiveCartierDivisor (I.comap f).subschemeι
  /-- The blowup is terminal among morphisms to `X` whose inverse-image center is an effective
  Cartier divisor. -/
  lift_unique {Y : Scheme.{u}} (g : Y ⟶ X)
      (_ : AlgebraicGeometry.IsEffectiveCartierDivisor (I.comap g).subschemeι) :
    ExistsUnique fun h : Y ⟶ X' ↦ h ≫ f = g

/-- The blowup universal property produces a unique factorization through the blowup for every
map to `X` whose inverse-image center is an effective Cartier divisor. -/
@[stacks 0806 "unique lift"]
theorem IsBlowup.existsUnique_lift {f : X' ⟶ X} [h : IsBlowup f I]
    {Y : Scheme.{u}} (g : Y ⟶ X)
    (hg : AlgebraicGeometry.IsEffectiveCartierDivisor (I.comap g).subschemeι) :
    ExistsUnique fun h' : Y ⟶ X' ↦ h' ≫ f = g :=
  h.lift_unique g hg

/-- A blowup morphism restricts to an isomorphism over the complement of the support of its
center. -/
theorem IsBlowup.isIso_restrict_compl_support {f : X' ⟶ X} [IsBlowup f I] :
    IsIso (f ∣_ ⟨(I.support : Set X)ᶜ, I.support.2.isOpen_compl⟩) := sorry

/-- A center for a `U`-admissible blowup is a finitely presented closed subscheme of `X` disjoint
from the open subscheme `U`, together with a blowup structure on the morphism. -/
@[stacks 080K "admissible center"]
class IsAdmissibleBlowupCenter (U : X.Opens) (f : X' ⟶ X) (I : X.IdealSheafData) : Prop
    extends IsBlowup f I where
  /-- The closed subscheme defining the center is locally of finite presentation over `X`. -/
  locallyOfFinitePresentation_subschemeι :
    LocallyOfFinitePresentation I.subschemeι
  /-- The center is disjoint from the open subscheme `U`. -/
  disjoint_support :
    Disjoint (I.support : Set X) U

/-- An admissible center is locally of finite presentation over the base scheme. -/
theorem IsAdmissibleBlowupCenter.locallyOfFinitePresentation {U : X.Opens} {f : X' ⟶ X}
    [h : IsAdmissibleBlowupCenter U f I] :
    LocallyOfFinitePresentation I.subschemeι :=
  h.locallyOfFinitePresentation_subschemeι

/-- An admissible center exhibits the given morphism as a blowup in that center. -/
theorem IsAdmissibleBlowupCenter.isBlowup {U : X.Opens} {f : X' ⟶ X}
    [h : IsAdmissibleBlowupCenter U f I] :
    IsBlowup f I :=
  h.toIsBlowup

/-- A center is admissible exactly when it is a blowup center of finite presentation disjoint from
the chosen open subscheme. -/
theorem isAdmissibleBlowupCenter_iff (U : X.Opens) (f : X' ⟶ X) (I : X.IdealSheafData) :
    IsAdmissibleBlowupCenter U f I ↔
      IsBlowup f I ∧
        LocallyOfFinitePresentation I.subschemeι ∧
        Disjoint (I.support : Set X) U := by
  constructor
  · intro h
    exact ⟨h.toIsBlowup, h.locallyOfFinitePresentation_subschemeι, h.disjoint_support⟩
  · rintro ⟨hblowup, hfp, hdisjoint⟩
    exact
      { toIsBlowup := hblowup
        locallyOfFinitePresentation_subschemeι := hfp
        disjoint_support := hdisjoint }

/-- A morphism `f : X' ⟶ X` is a `U`-admissible blowup when it is the blowup in a finitely
presented closed subscheme disjoint from `U`. -/
@[stacks 080K]
def IsAdmissibleBlowup (U : X.Opens) (f : X' ⟶ X) : Prop :=
  ∃ I : X.IdealSheafData, IsAdmissibleBlowupCenter U f I

/-- A `U`-admissible blowup is obtained from any admissible center. -/
theorem IsAdmissibleBlowup.mk {U : X.Opens} {f : X' ⟶ X}
    (I : X.IdealSheafData) [IsAdmissibleBlowupCenter U f I] :
    IsAdmissibleBlowup U f :=
  ⟨I, inferInstance⟩

/-- An admissible blowup comes equipped with an admissible center. -/
theorem IsAdmissibleBlowup.exists_center {U : X.Opens} {f : X' ⟶ X}
    (hf : IsAdmissibleBlowup U f) :
    ∃ I : X.IdealSheafData, IsAdmissibleBlowupCenter U f I :=
  hf

/-- A `U`-admissible blowup admits a center that is finitely presented, disjoint from `U`, and
for which the morphism is a blowup. -/
theorem IsAdmissibleBlowup.exists_center_spec {U : X.Opens} {f : X' ⟶ X}
    (hf : IsAdmissibleBlowup U f) :
    ∃ I : X.IdealSheafData,
      IsBlowup f I ∧
        LocallyOfFinitePresentation I.subschemeι ∧
        Disjoint (I.support : Set X) U := by
  rcases hf with ⟨I, hI⟩
  exact ⟨I, hI.toIsBlowup, hI.locallyOfFinitePresentation_subschemeι, hI.disjoint_support⟩

/-- A morphism is `U`-admissible exactly when it admits a finitely presented center disjoint from
`U` for which it satisfies the blowup universal property. -/
theorem isAdmissibleBlowup_iff (U : X.Opens) (f : X' ⟶ X) :
    IsAdmissibleBlowup U f ↔
      ∃ I : X.IdealSheafData,
        IsBlowup f I ∧
          LocallyOfFinitePresentation I.subschemeι ∧
          Disjoint (I.support : Set X) U := by
  constructor
  · exact IsAdmissibleBlowup.exists_center_spec
  · rintro ⟨I, hblowup, hfp, hdisjoint⟩
    exact ⟨I, (isAdmissibleBlowupCenter_iff U f I).2 ⟨hblowup, hfp, hdisjoint⟩⟩

end


end AlgebraicGeometry

namespace AlgebraicGeometry

namespace IsBlowup

/-- Pulling the center of a blowup back along the blowup morphism gives an effective Cartier
divisor. -/
instance instIsEffectiveCartierDivisor
    {X X' : Scheme.{u}} {I : X.IdealSheafData}
    {f : X' ⟶ X} [h : IsBlowup f I] :
    AlgebraicGeometry.IsEffectiveCartierDivisor (I.comap f).subschemeι :=
  h.toIsEffectiveCartierDivisor

/-- The restriction of a blowup morphism to the complement of its center is canonically
registered as an isomorphism. -/
instance instIsIsoRestrictComplSupport
    {X X' : Scheme.{u}} {I : X.IdealSheafData}
    {f : X' ⟶ X} [IsBlowup f I] :
    CategoryTheory.IsIso (f ∣_ ⟨(I.support : Set X)ᶜ, I.support.2.isOpen_compl⟩) :=
  AlgebraicGeometry.IsBlowup.isIso_restrict_compl_support

end IsBlowup

end AlgebraicGeometry
