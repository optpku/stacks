/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Additive
public import ReasLib.AlgebraicGeometry.ChowCohomology.Restriction
public import ReasLib.AlgebraicGeometry.BivariantClass.Composition
public import ReasLib.AlgebraicGeometry.BivariantClass.ProperPushforward

/-!
# Homogeneous cutoff bivariant classes

The carrier is ambient below the cutoff and relative from the cutoff onward.
The three mixed operations are the actual bivariant composition and restriction
maps. No associative multiplication on an arbitrary fixed cutoff is asserted.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- The degree-`n` part of the cutoff family: ambient Chow cohomology below `p`, and
bivariant classes on the closed immersion from degree `p` onward. -/
def Cutoff
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (p : ℕ) (n : ℤ) : Type (u + 1) :=
  if n < (p : ℤ) then ChowCohomology.degree δ X.hom n else BivariantClass δ i n

/-- The cutoff family is the stated degreewise conditional. -/
theorem cutoff_def
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (p : ℕ) (n : ℤ) :
    Cutoff δ i p n =
      (if n < (p : ℤ) then ChowCohomology.degree δ X.hom n
        else BivariantClass δ i n) := sorry

namespace Cutoff

/-- Every homogeneous cutoff degree has its canonical additive commutative group. -/
instance instAddCommGroup
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (p : ℕ) (n : ℤ) :
    AddCommGroup (Cutoff δ i p n) :=
  if h : n < (p : ℤ) then
    Eq.mpr (congrArg AddCommGroup (if_pos h))
      (inferInstance : AddCommGroup (ChowCohomology.degree δ X.hom n))
  else
    Eq.mpr (congrArg AddCommGroup (if_neg h))
      (pointwiseAddCommGroup δ i n)

/-- Insert an ambient class into a cutoff degree known to lie below the cutoff. -/
def ofAmbient
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] {p : ℕ} {n : ℤ}
    (h : n < (p : ℤ)) :
    ChowCohomology.degree δ X.hom n →+ Cutoff δ i p n where
  toFun := fun c ↦ Eq.mpr (if_pos h) c
  map_zero' := sorry
  map_add' := sorry

/-- Recover the ambient class represented by a cutoff degree below the cutoff. -/
def toAmbient
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] {p : ℕ} {n : ℤ}
    (h : n < (p : ℤ)) :
    Cutoff δ i p n →+ ChowCohomology.degree δ X.hom n where
  toFun := fun c ↦ Eq.mp (if_pos h) c
  map_zero' := sorry
  map_add' := sorry

/-- Ambient insertion followed by ambient projection is the identity. -/
theorem toAmbient_ofAmbient
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] {p : ℕ} {n : ℤ}
    (h : n < (p : ℤ)) (c : ChowCohomology.degree δ X.hom n) :
    toAmbient δ i h (ofAmbient δ i h c) = c := sorry

/-- Insert a relative bivariant class into a cutoff degree at or above the cutoff. -/
def ofRelative
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] {p : ℕ} {n : ℤ}
    (h : ¬n < (p : ℤ)) :=
  -- Local instance justification (instance diamond): BivariantClass uses named pointwiseAddCommGroup; a global instance diamonds with ChowCohomology.instAddCommGroupDegree.
  letI := pointwiseAddCommGroup δ i n
  ({ toFun := fun c ↦ Eq.mpr (if_neg h) c
     map_zero' := sorry
     map_add' := sorry } : BivariantClass δ i n →+ Cutoff δ i p n)

/-- Recover the relative class represented by a cutoff degree at or above the cutoff. -/
def toRelative
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] {p : ℕ} {n : ℤ}
    (h : ¬n < (p : ℤ)) :=
  -- Local instance justification (instance diamond): BivariantClass uses named pointwiseAddCommGroup; a global instance diamonds with ChowCohomology.instAddCommGroupDegree.
  letI := pointwiseAddCommGroup δ i n
  ({ toFun := fun c ↦ Eq.mp (if_neg h) c
     map_zero' := sorry
     map_add' := sorry } : Cutoff δ i p n →+ BivariantClass δ i n)

/-- Relative insertion followed by relative projection is the identity. -/
theorem toRelative_ofRelative
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] {p : ℕ} {n : ℤ}
    (h : ¬n < (p : ℤ)) (c : BivariantClass δ i n) :
    toRelative δ i h (ofRelative δ i h c) = c := sorry

/-- Restriction of an ambient class on `X` to an ambient class on `Z`. -/
def ambientRestriction
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (n : ℤ) :
    ChowCohomology.degree δ X.hom n →+ ChowCohomology.degree δ Z.hom n where
  toFun := BivariantClass.restrict δ i (𝟙 Z) i IsPullback.of_id_snd n
  map_zero' := sorry
  map_add' := sorry

/-- Ambient restriction is the identity-square specialization of bivariant restriction. -/
theorem ambientRestriction_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (n : ℤ)
    (c : ChowCohomology.degree δ X.hom n) :
    ambientRestriction δ i n c =
      BivariantClass.restrict δ i (𝟙 Z) i IsPullback.of_id_snd n c := sorry

/-- The self-intersection square of a closed immersion is cartesian. -/
theorem relativeRestrictionSquare
    {S : Scheme.{u}} {Z X : Over S} (i : Z ⟶ X) [IsClosedImmersion i.left] :
    IsPullback (𝟙 Z : Z ⟶ Z).left (𝟙 Z : Z ⟶ Z).left i.left i.left := sorry

/-- Restriction of a relative bivariant class to the identity of its source. -/
def relativeRestriction
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (n : ℤ) :=
  -- Local instance justification (instance diamond): BivariantClass uses named pointwiseAddCommGroup; a global instance diamonds with ChowCohomology.instAddCommGroupDegree.
  letI := pointwiseAddCommGroup δ i n
  ({ toFun := BivariantClass.restrictToSource δ i n
     map_zero' := sorry
     map_add' := sorry } : BivariantClass δ i n →+ ChowCohomology.degree δ Z.hom n)

/-- Relative restriction is restriction of a closed-immersion class to its source. -/
theorem relativeRestriction_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (n : ℤ) (c : BivariantClass δ i n) :
    relativeRestriction δ i n c = BivariantClass.restrictToSource δ i n c := sorry

/-- Proper pushforward of a relative class to an ambient class on the target. -/
def relativePushforward
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (n : ℤ) :=
  -- Local instance justification (instance diamond): BivariantClass uses named pointwiseAddCommGroup; a global instance diamonds with ChowCohomology.instAddCommGroupDegree.
  letI := pointwiseAddCommGroup δ i n
  ({ toFun := BivariantClass.properPushforwardToTarget δ i n
     map_zero' := sorry
     map_add' := sorry } : BivariantClass δ i n →+ ChowCohomology.degree δ X.hom n)

/-- Relative pushforward is the proper pushforward to the target identity. -/
theorem relativePushforward_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (n : ℤ) (c : BivariantClass δ i n) :
    relativePushforward δ i n c = BivariantClass.properPushforwardToTarget δ i n c := rfl

/-- Composition gives the product of a relative class and an ambient class. -/
def relativeMulAmbient
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (a b : ℤ) :=
  -- Local instance justification (instance diamond): BivariantClass uses named pointwiseAddCommGroup; a global instance diamonds with ChowCohomology.instAddCommGroupDegree.
  letI := pointwiseAddCommGroup δ i a
  -- Local instance justification (instance diamond): same explicit pointwise group on the composite degree.
  letI := pointwiseAddCommGroup δ i (a + b)
  ({ toFun := fun c ↦
      { toFun := fun d ↦ (Category.comp_id i) ▸ BivariantClass.comp δ i (𝟙 X) c d
        map_zero' := sorry
        map_add' := sorry }
     map_zero' := sorry
     map_add' := sorry } :
    BivariantClass δ i a →+ ChowCohomology.degree δ X.hom b →+
      BivariantClass δ i (a + b))

/-- The relative-ambient product is bivariant composition followed by identity transport. -/
theorem relativeMulAmbient_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] {a b : ℤ}
    (c : BivariantClass δ i a) (d : ChowCohomology.degree δ X.hom b) :
    relativeMulAmbient δ i a b c d =
      (Category.comp_id i) ▸ BivariantClass.comp δ i (𝟙 X) c d := sorry

/-- Restriction to `Z`, followed by composition, gives the product of an ambient class
and a relative class. -/
def ambientMulRelative
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (a b : ℤ) :=
  -- Local instance justification (instance diamond): BivariantClass uses named pointwiseAddCommGroup; a global instance diamonds with ChowCohomology.instAddCommGroupDegree.
  letI := pointwiseAddCommGroup δ i b
  -- Local instance justification (instance diamond): same explicit pointwise group on the composite degree.
  letI := pointwiseAddCommGroup δ i (a + b)
  ({ toFun := fun c ↦
      { toFun := fun d ↦ (Category.id_comp i) ▸
          BivariantClass.comp δ (𝟙 Z) i (ambientRestriction δ i a c) d
        map_zero' := sorry
        map_add' := sorry }
     map_zero' := sorry
     map_add' := sorry } :
    ChowCohomology.degree δ X.hom a →+ BivariantClass δ i b →+
      BivariantClass δ i (a + b))

/-- The ambient-relative product restricts the ambient factor and then composes. -/
theorem ambientMulRelative_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] {a b : ℤ}
    (c : ChowCohomology.degree δ X.hom a) (d : BivariantClass δ i b) :
    ambientMulRelative δ i a b c d = (Category.id_comp i) ▸
      BivariantClass.comp δ (𝟙 Z) i (ambientRestriction δ i a c) d := sorry

/-- Restricting the first relative factor to `Z` and composing gives the product of two
relative classes. -/
def relativeMul
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (a b : ℤ) :=
  -- Local instance justification (instance diamond): BivariantClass uses named pointwiseAddCommGroup; a global instance diamonds with ChowCohomology.instAddCommGroupDegree.
  letI := pointwiseAddCommGroup δ i a
  -- Local instance justification (instance diamond): same explicit pointwise group on the second factor.
  letI := pointwiseAddCommGroup δ i b
  -- Local instance justification (instance diamond): same explicit pointwise group on the composite degree.
  letI := pointwiseAddCommGroup δ i (a + b)
  ({ toFun := fun c ↦
      { toFun := fun d ↦ (Category.id_comp i) ▸
          BivariantClass.comp δ (𝟙 Z) i (relativeRestriction δ i a c) d
        map_zero' := sorry
        map_add' := sorry }
     map_zero' := sorry
     map_add' := sorry } :
    BivariantClass δ i a →+ BivariantClass δ i b →+
      BivariantClass δ i (a + b))

/-- The relative-relative product is restriction to the source followed by composition. -/
theorem relativeMul_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] {a b : ℤ}
    (c : BivariantClass δ i a) (d : BivariantClass δ i b) :
    relativeMul δ i a b c d = (Category.id_comp i) ▸
      BivariantClass.comp δ (𝟙 Z) i (relativeRestriction δ i a c) d := sorry

end Cutoff

end AlgebraicGeometry.BivariantClass
