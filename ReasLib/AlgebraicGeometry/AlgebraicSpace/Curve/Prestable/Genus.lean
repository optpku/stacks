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
          (higherDirectImageOne (hom P)) := Iff.rfl

/-- The prestable genus-`g` locus is the intersection of the prestable locus
with the genus-`g` locus. -/
theorem prestableOfGenus_iff_ofGenus (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    prestableOfGenus g S P ↔ prestable S P ∧ ofGenus g S P := by
  constructor
  · intro h
    exact ⟨h.1, ((prestable_iff_nodal_h0Dim1 P).mp h.1).2, h.2⟩
  · intro h
    exact ⟨h.1, h.2.2⟩

/-- A family in the prestable genus-`g` locus is prestable. -/
theorem prestableOfGenus_le_prestable (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    prestableOfGenus g S P → prestable S P := fun h ↦ h.1

/-- A family in the prestable genus-`g` locus belongs to the genus-`g` locus. -/
theorem prestableOfGenus_le_ofGenus (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    prestableOfGenus g S P → ofGenus g S P := fun h ↦
  ((prestableOfGenus_iff_ofGenus g P).mp h).2

/-- A prestable family over a nonempty base belongs to at most one
fixed-genus locus. -/
theorem eq_of_mem_prestableOfGenus {S : Scheme.{u}} {P : Obj S} {g g' : ℕ}
    (hbase : Nonempty (base P).left)
    (hg : prestableOfGenus g S P) (hg' : prestableOfGenus g' S P) : g = g' :=
  eq_of_mem_ofGenus hbase (prestableOfGenus_le_ofGenus g P hg)
    (prestableOfGenus_le_ofGenus g' P hg')

/-- Membership in the prestable genus-`g` locus is invariant under
isomorphisms of families. -/
instance instIsClosedUnderIsomorphisms_prestableOfGenus (g : ℕ) (S : Scheme.{u}) :
    (prestableOfGenus g S).IsClosedUnderIsomorphisms where
  of_iso := by
    intro P Q e h
    obtain ⟨hprestable, hgenus⟩ := (prestableOfGenus_iff_ofGenus g P).mp h
    exact (prestableOfGenus_iff_ofGenus g Q).mpr
      ⟨(prestable S).prop_of_iso e hprestable, (ofGenus g S).prop_of_iso e hgenus⟩

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
              prestableOfGenus g S Q ↔ Set.range (baseMap φ).left ⊆ U g := by
  obtain ⟨U, hcover, hdisjoint, hclopen, hgenus⟩ :=
    exists_ofGenus_clopen_decomposition P ((prestable_iff_nodal_h0Dim1 P).mp h).2
  obtain ⟨V, hV⟩ := exists_prestable_open P
  have hVall (x : (base P).left) : x ∈ V :=
    (hV (𝟙 P)).mp h ⟨x, rfl⟩
  refine ⟨U, hcover, hdisjoint, hclopen, ?_⟩
  intro g Q φ
  constructor
  · intro hg
    exact (hgenus g φ).mp (prestableOfGenus_le_ofGenus g Q hg)
  · intro hrange
    exact (prestableOfGenus_iff_ofGenus g Q).mpr
      ⟨(hV φ).mpr (fun x _ ↦ hVall x), (hgenus g φ).mpr hrange⟩

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
          SchemeOverField.genus X hdim1 hΓ = g := by
  rw [prestableOfGenus_iff_ofGenus,
    classifying_factorsThrough_prestable_iff_scheme, ofGenus_iff_scheme]
  constructor
  · rintro ⟨⟨hnodal, _, _⟩, hgenus⟩
    exact ⟨hnodal, hgenus⟩
  · rintro ⟨hnodal, hdim1, hΓ, hgenus⟩
    exact ⟨⟨hnodal, hdim1, hΓ⟩, ⟨hdim1, hΓ, hgenus⟩⟩

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
