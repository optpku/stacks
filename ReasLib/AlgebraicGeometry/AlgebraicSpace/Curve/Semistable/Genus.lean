/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.SemistableLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Prestable.Genus

/-!
# Genus loci of semistable families of curves

Semistable families decompose over their bases into pairwise disjoint clopen
loci of fixed positive genus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of semistable families whose first structure-sheaf
higher direct image is finite locally free of rank `g`. -/
def semistableOfGenus (g : ℕ) (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦
    semistable S P ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank g (higherDirectImageOne (hom P))

/-- A family belongs to the semistable genus-`g` locus precisely when it is
semistable and its first structure-sheaf higher direct image has rank `g`. -/
theorem semistableOfGenus_iff (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    semistableOfGenus g S P ↔
      semistable S P ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank g
          (higherDirectImageOne (hom P)) := sorry

/-- A family in the semistable genus-`g` locus is semistable. -/
theorem semistableOfGenus_le_semistable (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    semistableOfGenus g S P → semistable S P := sorry

/-- A semistable family over a nonempty base belongs to at most one
fixed-genus locus. -/
theorem eq_of_mem_semistableOfGenus {S : Scheme.{u}} {P : Obj S} {g g' : ℕ}
    (hbase : Nonempty (base P).left)
    (hg : semistableOfGenus g S P) (hg' : semistableOfGenus g' S P) :
    g = g' := sorry

/-- Membership in the semistable genus-`g` locus is invariant under
isomorphisms of families. -/
instance instIsClosedUnderIsomorphisms_semistableOfGenus
    (g : ℕ) (S : Scheme.{u}) :
    (semistableOfGenus g S).IsClosedUnderIsomorphisms := sorry

/-- Every semistable family has a pairwise disjoint clopen cover of its base
by positive-genus loci, representing fixed-genus semistability under every
cartesian morphism of families. -/
theorem exists_semistableOfGenus_clopen_decomposition {S : Scheme.{u}} (P : Obj S)
    (h : semistable S P) :
    ∃ U : ℕ → (base P).left.Opens,
      iSup U = ⊤ ∧
        Pairwise (fun n n' ↦ Disjoint (U n : Set (base P).left) (U n')) ∧
          (∀ n, IsClopen (U n : Set (base P).left)) ∧
            ∀ n, ∀ {Q : Obj S} (φ : Q ⟶ P),
              semistableOfGenus (n + 1) S Q ↔ Set.range (baseMap φ).left ⊆ U n := sorry

/-- A proper scheme of dimension at most one over a field belongs to the
semistable genus-`g` locus for `g ≥ 1` precisely when it is at-worst-nodal,
has dimension one, has bijective canonical global-sections map, has genus `g`,
and has no rational tails. -/
theorem classifying_factorsThrough_semistableOfGenus_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) (hg : 1 ≤ g) :
    semistableOfGenus g (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          SchemeOverField.genus X hdim1 hΓ = g ∧
            ¬ Nonempty (SchemeOverField.RationalTail X) := sorry

/-- A proper scheme of dimension at most one over a field belongs to the
semistable genus-`g` locus for `g ≥ 1` precisely when it is at-worst-nodal,
has dimension one, has bijective canonical global-sections map, has genus `g`,
and has invertible dualizing module with all integral tensor powers of
exponent at least two globally generated. -/
theorem classifying_factorsThrough_semistableOfGenus_iff_scheme_dualizing
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) (hg : 1 ≤ g) :
    semistableOfGenus g (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          SchemeOverField.genus X hdim1 hΓ = g ∧
            dualizingTensorPowersGloballyGenerated X := sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
