/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap73.Definition_73_4_5_Site
public import stacks_project.Chap73.Definition_73_8_1_PhCovering

/-!
# Chosen big ph sites of algebraic spaces

The ph covering class of algebraic spaces over a scheme `S` is packaged as a
precoverage whose covering presieves are represented by `PhCovering` families.
A chosen big ph site is a Lemma 3.11.1 cardinal truncation of that class.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The ph precoverage on algebraic spaces over `S`: covering presieves are those
represented by an indexed ph covering family. -/
def phPrecoverage : Precoverage (AlgebraicSpace S) where
  coverings X :=
    {R | ∃ (ι : Type (u + 1)) (Y : ι → AlgebraicSpace S) (f : ∀ i, Y i ⟶ X),
      R = Presieve.ofArrows Y f ∧ PhCovering Y f}

/-- A presieve belongs to `phPrecoverage` if and only if it is represented by an
indexed ph covering family. -/
theorem mem_phPrecoverage_iff {X : AlgebraicSpace S} {R : Presieve X} :
    R ∈ phPrecoverage X ↔
      ∃ (ι : Type (u + 1)) (Y : ι → AlgebraicSpace S) (f : ∀ i, Y i ⟶ X),
        R = Presieve.ofArrows Y f ∧ PhCovering Y f :=
  sorry

/-- An indexed family belongs to `phPrecoverage` if and only if it is a ph
covering. -/
theorem ofArrows_mem_phPrecoverage_iff {X : AlgebraicSpace S}
    {ι : Type (u + 1)} {Y : ι → AlgebraicSpace S} (f : ∀ i, Y i ⟶ X) :
    Presieve.ofArrows Y f ∈ phPrecoverage X ↔ PhCovering Y f :=
  sorry

/-- The ph covering class of algebraic spaces over `S` satisfies the site
axioms. -/
instance phPrecoverage.instIsSite :
    (phPrecoverage : Precoverage (AlgebraicSpace S)).IsSite :=
  sorry

/-- A big ph site of algebraic spaces over `S` is a chosen big site for the ph
covering class. -/
abbrev ChosenBigPhSite (S : Scheme.{u}) :=
  ChosenBigSite (phPrecoverage : Precoverage (AlgebraicSpace S))

/-- Sets Lemma 3.11.1 supplies a chosen big ph site of algebraic spaces over
`S`. -/
theorem ChosenBigPhSite.exists (S : Scheme.{u}) :
    Nonempty (ChosenBigPhSite S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
