/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Prestable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Genus

/-!
# Genus loci of prestable families of curves

Prestable families decompose over their bases into pairwise disjoint clopen
loci of fixed genus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of prestable families whose first structure-sheaf
higher direct image is finite locally free of rank `g`. -/
def prestableOfGenus (g : ℕ) (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦
    prestable S P ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank g (higherDirectImageOne (hom P))

/-- A family belongs to the prestable genus-`g` locus precisely when it is
prestable and its first structure-sheaf higher direct image has rank `g`. -/
theorem prestableOfGenus_iff (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    prestableOfGenus g S P ↔
      prestable S P ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank g
          (higherDirectImageOne (hom P)) := sorry

/-- The prestable genus-`g` locus is the intersection of the prestable locus
with the genus-`g` locus. -/
theorem prestableOfGenus_iff_ofGenus (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    prestableOfGenus g S P ↔ prestable S P ∧ ofGenus g S P := sorry

/-- A family in the prestable genus-`g` locus is prestable. -/
theorem prestableOfGenus_le_prestable (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    prestableOfGenus g S P → prestable S P := sorry

/-- A family in the prestable genus-`g` locus belongs to the genus-`g` locus. -/
theorem prestableOfGenus_le_ofGenus (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    prestableOfGenus g S P → ofGenus g S P := sorry

/-- A prestable family over a nonempty base belongs to at most one
fixed-genus locus. -/
theorem eq_of_mem_prestableOfGenus {S : Scheme.{u}} {P : Obj S} {g g' : ℕ}
    (hbase : Nonempty (base P).left)
    (hg : prestableOfGenus g S P) (hg' : prestableOfGenus g' S P) : g = g' := sorry

/-- Membership in the prestable genus-`g` locus is invariant under
isomorphisms of families. -/
instance instIsClosedUnderIsomorphisms_prestableOfGenus (g : ℕ) (S : Scheme.{u}) :
    (prestableOfGenus g S).IsClosedUnderIsomorphisms := sorry

/-- Every prestable family has a pairwise disjoint clopen cover of its base
by genus loci, representing fixed-genus prestability under every cartesian
morphism of families. -/
theorem exists_prestableOfGenus_clopen_decomposition {S : Scheme.{u}} (P : Obj S)
    (h : prestable S P) :
    ∃ U : ℕ → (base P).left.Opens,
      iSup U = ⊤ ∧
        Pairwise (fun g g' ↦ Disjoint (U g : Set (base P).left) (U g')) ∧
          (∀ g, IsClopen (U g : Set (base P).left)) ∧
            ∀ g, ∀ {Q : Obj S} (φ : Q ⟶ P),
              prestableOfGenus g S Q ↔ Set.range (baseMap φ).left ⊆ U g := sorry

/-- A proper scheme of dimension at most one over a field belongs to the
prestable genus-`g` locus precisely when it is at-worst-nodal, has dimension
one, has bijective canonical global-sections map, and has genus `g`. -/
theorem classifying_factorsThrough_prestableOfGenus_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) :
    prestableOfGenus g (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          SchemeOverField.genus X hdim1 hΓ = g := sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
