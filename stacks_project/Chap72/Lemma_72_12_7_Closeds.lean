module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Notation
public import Mathlib.Topology.Sets.Closeds
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap72.«72_12_5_1_Galois»

/-!
# Closed subsets of a Galois field-extension base change of an algebraic space

Closed subsets of `|X|` and of the field-extension base change `|X_K|` are
bundled as `TopologicalSpace.Closeds`. This leaf exposes pullback along
`|X_K| → |X|` and along the Galois-induced automorphisms of `X_K`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace FieldExtension.Galois.Closeds

/-- Pull a closed subset of `|X|` back along `|X_K| → |X|`. -/
noncomputable abbrev preimage
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (of k))} (T : Closeds (Points X)) :
    Closeds (Points (FieldExtension.baseChange k K X)) :=
  T.preimage (Points.continuous_map (FieldExtension.baseChangeSnd k K X))

/-- Pull a closed subset of `|X_K|` back along the automorphism induced by
`σ : Gal(K/k)`. -/
noncomputable abbrev galoisPreimage
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (of k))} (σ : Gal(K/k))
    (Tbar : Closeds (Points (FieldExtension.baseChange k K X))) :
    Closeds (Points (FieldExtension.baseChange k K X)) :=
  Tbar.preimage (Points.continuous_map (FieldExtension.Galois.map k K X σ))

/-- The underlying set of a closed subset pulled back from `|X|` is the ordinary
preimage along `|X_K| → |X|`. -/
theorem coe_preimage
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (of k))} (T : Closeds (Points X)) :
    (preimage k K T : Set (Points (FieldExtension.baseChange k K X))) =
      Points.map (FieldExtension.baseChangeSnd k K X) ⁻¹' (T : Set (Points X)) :=
  sorry

/-- The underlying set of a Galois closed preimage is the ordinary preimage along
the induced map on points. -/
theorem coe_galoisPreimage
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (of k))} (σ : Gal(K/k))
    (Tbar : Closeds (Points (FieldExtension.baseChange k K X))) :
    (galoisPreimage k K σ Tbar : Set (Points (FieldExtension.baseChange k K X))) =
      Points.map (FieldExtension.Galois.map k K X σ) ⁻¹'
        (Tbar : Set (Points (FieldExtension.baseChange k K X))) :=
  sorry

/-- Galois-invariance of a closed subset of `|X_K|` may be checked as a preimage
equality or as an image equality. -/
theorem galoisPreimage_eq_iff_image
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (of k))} (σ : Gal(K/k))
    (Tbar : Closeds (Points (FieldExtension.baseChange k K X))) :
    galoisPreimage k K σ Tbar = Tbar ↔
      Points.map (FieldExtension.Galois.map k K X σ) '' (Tbar : Set _) =
        (Tbar : Set _) :=
  sorry

/-- A closed subset of `|X_K|` stable under every Galois closed preimage is the
inverse image of a closed subset of `|X|`. -/
theorem exists_preimage_eq_of_preimage
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (X : AlgebraicSpace (Spec (of k)))
    (Tbar : Closeds (Points (FieldExtension.baseChange k K X)))
    (h_preimage : ∀ σ : Gal(K/k), galoisPreimage k K σ Tbar = Tbar) :
    ∃ T : Closeds (Points X), preimage k K T = Tbar :=
  sorry

end FieldExtension.Galois.Closeds
end AlgebraicGeometry.AlgebraicSpace
