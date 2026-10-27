/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.HigherDirectImage
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import Mathlib.Topology.Clopen

/-!
# Genus loci of families of curves

Curve families with universally trivial structure-sheaf pushforward and
one-dimensional fibres decompose into clopen loci of fixed genus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of families of curves with universally trivial
`𝒪_S ⟶ f_* 𝒪_X`, fibres of dimension `1`, and `R^1 f_* 𝒪_X` finite locally
free of rank `g`, corresponding to the open-and-closed substack `𝒞urves_g`. -/
def ofGenus (g : ℕ) (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦
    h0Dim1 S P ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank g (higherDirectImageOne (hom P))

/-- Membership in `ofGenus g` means the unit `𝒪_S ⟶ f_* 𝒪_X` is an isomorphism
after every base change, including the identity, every fibre has dimension `1`,
and `R^1 f_* 𝒪_X` is finite locally free of rank `g`. -/
theorem ofGenus_iff (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    ofGenus g S P ↔
      (∀ {Z : AlgebraicSpace S} (φ : Z ⟶ ofOver (base P)),
          IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) φ))) ∧
        (∀ y : Points (ofOver (base P)), fiberDimension (hom P) y = 1) ∧
          SheafOfModules.IsFiniteLocallyFreeOfRank g
            (higherDirectImageOne (hom P)) := sorry

/-- The `ofGenus` property of families of curves is closed under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_ofGenus (g : ℕ) (S : Scheme.{u}) :
    (ofGenus g S).IsClosedUnderIsomorphisms := sorry

/-- Membership in `ofGenus g` implies membership in `h0Dim1`. -/
theorem ofGenus_le_h0Dim1 (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    ofGenus g S P → h0Dim1 S P := sorry

/-- A family of curves over a nonempty base has at most one genus. -/
theorem eq_of_mem_ofGenus {S : Scheme.{u}} {P : Obj S} {g g' : ℕ}
    (hbase : Nonempty (base P).left)
    (hg : ofGenus g S P) (hg' : ofGenus g' S P) : g = g' := sorry


/-- A proper scheme of dimension at most one over a field belongs to the genus
`g` locus precisely when it has dimension one, its canonical global-sections map
is bijective, and its genus equals `g`. -/
theorem ofGenus_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) :
    ofGenus g (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      ∃ (hdim1 : topologicalKrullDim X.left = 1)
        (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
        SchemeOverField.genus X hdim1 hΓ = g := sorry


/-- Every curve family with universally trivial structure-sheaf pushforward and
one-dimensional fibres has a pairwise disjoint clopen cover of its base by genus
loci, representing each fixed-genus property under every cartesian morphism of
families. -/
theorem exists_ofGenus_clopen_decomposition {S : Scheme.{u}} (P : Obj S)
    (h : h0Dim1 S P) :
    ∃ U : ℕ → (base P).left.Opens,
      iSup U = ⊤ ∧
        Pairwise (fun g g' ↦ Disjoint (U g : Set (base P).left) (U g')) ∧
          (∀ g, IsClopen (U g : Set (base P).left)) ∧
            ∀ g, ∀ {Q : Obj S} (φ : Q ⟶ P),
              ofGenus g S Q ↔ Set.range (baseMap φ).left ⊆ U g := sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
