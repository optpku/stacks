/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.QuasiCompact

@[expose] public section

open CategoryTheory
open MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.GroupScheme

variable {k : Type u} [Field k]

/-- There is an algebraically closed field extension whose cardinality strictly exceeds two
prescribed bounds. -/
theorem existsLargeAlgClosedFieldExtension (κ₁ κ₂ : Cardinal.{u}) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : IsAlgClosed K),
      κ₁ < Cardinal.mk K ∧ κ₂ < Cardinal.mk K :=
  Field.exists_algClosed_extension_cardinal_gt k κ₁ κ₂

/-- Over an algebraically closed field, a closed point with algebraic residue field is the image
of the closed point under a section of the structure morphism. -/
theorem exists_rationalPoint_of_closedPoint_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : SchemeOverField K) (x : closedPoints G.left)
    (hx : Scheme.Hom.ResidueField.IsAlgebraicOverSpec G.hom x.1) :
    ∃ gLeft : Spec (CommRingCat.of K) ⟶ G.left,
      gLeft ≫ G.hom = 𝟙 _ ∧ gLeft (IsLocalRing.closedPoint K) = x.1 :=
  Scheme.Hom.ResidueField.exists_section_through_closedPoint_of_isAlgClosed G x hx

/- Lemma 39.7.9: An irreducible group scheme over a field is quasi-compact. -/
@[stacks 0B7P] #check
  (AlgebraicGeometry.GroupScheme.instCompactSpaceOfIrreducible :
    ∀ {k : Type u} [Field k] (G : AlgebraicGeometry.SchemeOverField k) [GrpObj G]
      [IrreducibleSpace G.left], CompactSpace G.left)

end AlgebraicGeometry.GroupScheme
