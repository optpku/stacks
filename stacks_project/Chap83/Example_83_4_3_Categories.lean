/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap83.Definition_83_4_1_Quotient

/-!
# Standard full subcategories for categorical quotients

Standard `ObjectProperty` cuts of `Over B` used as the ambient category `C` in
`IsCategoricalQuotientIn`: separated, quasi-separated, locally separated, and
decent algebraic spaces over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace ObjectProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace PreRelation

/-- The full subcategory of algebraic spaces over `B` that are separated. -/
def isSeparated {S : Scheme.{u}} {B : AlgebraicSpace S} : ObjectProperty (Over B) :=
  fun X ↦ IsAbsolutelySeparated X.left

/-- Membership in `isSeparated` is the property that the underlying algebraic space is
absolutely separated. -/
theorem isSeparated_iff {S : Scheme.{u}} {B : AlgebraicSpace S} (X : Over B) :
    isSeparated X ↔ IsAbsolutelySeparated X.left :=
  sorry

/-- The full subcategory of algebraic spaces over `B` that are quasi-separated. -/
def isQuasiSeparated {S : Scheme.{u}} {B : AlgebraicSpace S} : ObjectProperty (Over B) :=
  fun X ↦ IsAbsolutelyQuasiSeparated X.left

/-- Membership in `isQuasiSeparated` is the property that the underlying algebraic space
is absolutely quasi-separated. -/
theorem isQuasiSeparated_iff {S : Scheme.{u}} {B : AlgebraicSpace S} (X : Over B) :
    isQuasiSeparated X ↔ IsAbsolutelyQuasiSeparated X.left :=
  sorry

/-- The full subcategory of algebraic spaces over `B` that are locally separated. -/
def isLocallySeparated {S : Scheme.{u}} {B : AlgebraicSpace S} : ObjectProperty (Over B) :=
  fun X ↦ IsAbsolutelyLocallySeparated X.left

/-- Membership in `isLocallySeparated` is the property that the underlying algebraic
space is absolutely locally separated. -/
theorem isLocallySeparated_iff {S : Scheme.{u}} {B : AlgebraicSpace S} (X : Over B) :
    isLocallySeparated X ↔ IsAbsolutelyLocallySeparated X.left :=
  sorry

/-- The full subcategory of algebraic spaces over `B` that are decent. -/
def isDecent {S : Scheme.{u}} {B : AlgebraicSpace S} : ObjectProperty (Over B) :=
  fun X ↦ IsDecent X.left

/-- Membership in `isDecent` is the property that the underlying algebraic space is
decent. -/
theorem isDecent_iff {S : Scheme.{u}} {B : AlgebraicSpace S} (X : Over B) :
    isDecent X ↔ IsDecent X.left :=
  sorry

/-- A morphism of algebraic spaces over a separated base `B` is a categorical quotient
in separated algebraic spaces when it is a categorical quotient in the full subcategory
of separated algebraic spaces over `B`. -/
abbrev IsCategoricalQuotientInSeparated {S : Scheme.{u}} {B : AlgebraicSpace S}
    [IsAbsolutelySeparated B] {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) : Prop :=
  P.IsCategoricalQuotientIn isSeparated φ

/-- A categorical quotient in separated algebraic spaces is a categorical quotient in
the full subcategory of separated algebraic spaces over `B`. -/
theorem isCategoricalQuotientInSeparated_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    [IsAbsolutelySeparated B] {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) :
    P.IsCategoricalQuotientInSeparated φ ↔ P.IsCategoricalQuotientIn isSeparated φ :=
  sorry

/-- A morphism of algebraic spaces over a quasi-separated base `B` is a categorical
quotient in quasi-separated algebraic spaces when it is a categorical quotient in the
full subcategory of quasi-separated algebraic spaces over `B`. -/
abbrev IsCategoricalQuotientInQuasiSeparated {S : Scheme.{u}} {B : AlgebraicSpace S}
    [IsAbsolutelyQuasiSeparated B] {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) : Prop :=
  P.IsCategoricalQuotientIn isQuasiSeparated φ

/-- A categorical quotient in quasi-separated algebraic spaces is a categorical quotient
in the full subcategory of quasi-separated algebraic spaces over `B`. -/
theorem isCategoricalQuotientInQuasiSeparated_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    [IsAbsolutelyQuasiSeparated B] {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) :
    P.IsCategoricalQuotientInQuasiSeparated φ ↔
      P.IsCategoricalQuotientIn isQuasiSeparated φ :=
  sorry

/-- A morphism of algebraic spaces over a locally separated base `B` is a categorical
quotient in locally separated algebraic spaces when it is a categorical quotient in the
full subcategory of locally separated algebraic spaces over `B`. -/
abbrev IsCategoricalQuotientInLocallySeparated {S : Scheme.{u}} {B : AlgebraicSpace S}
    [IsAbsolutelyLocallySeparated B] {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) :
    Prop :=
  P.IsCategoricalQuotientIn isLocallySeparated φ

/-- A categorical quotient in locally separated algebraic spaces is a categorical
quotient in the full subcategory of locally separated algebraic spaces over `B`. -/
theorem isCategoricalQuotientInLocallySeparated_iff {S : Scheme.{u}}
    {B : AlgebraicSpace S} [IsAbsolutelyLocallySeparated B] {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) :
    P.IsCategoricalQuotientInLocallySeparated φ ↔
      P.IsCategoricalQuotientIn isLocallySeparated φ :=
  sorry

/-- A morphism of algebraic spaces over a decent base `B` is a categorical quotient in
decent algebraic spaces when it is a categorical quotient in the full subcategory of
decent algebraic spaces over `B`. -/
abbrev IsCategoricalQuotientInDecent {S : Scheme.{u}} {B : AlgebraicSpace S}
    [IsDecent B] {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) : Prop :=
  P.IsCategoricalQuotientIn isDecent φ

/-- A categorical quotient in decent algebraic spaces is a categorical quotient in the
full subcategory of decent algebraic spaces over `B`. -/
theorem isCategoricalQuotientInDecent_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    [IsDecent B] {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) :
    P.IsCategoricalQuotientInDecent φ ↔ P.IsCategoricalQuotientIn isDecent φ :=
  sorry

end PreRelation
end AlgebraicGeometry.AlgebraicSpace
