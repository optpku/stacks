/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Genus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.GeometricallyReducedConnected

/-!
# Genus loci of geometrically reduced and connected curve families
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of families of curves with reduced, connected geometric
fibres of dimension `1` and `R¹ f_* 𝒪_X` finite locally free of rank `g`. -/
def geometricallyReducedConnectedDim1OfGenus (g : ℕ) (S : Scheme.{u}) :
    ObjectProperty (Obj S) :=
  fun P ↦
    geometricallyReducedConnectedDim1 S P ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank g (higherDirectImageOne (hom P))

/-- Membership in `geometricallyReducedConnectedDim1OfGenus g` means the family
lies in `geometricallyReducedConnectedDim1` and `R¹ f_* 𝒪_X` is finite locally
free of rank `g`. -/
theorem geometricallyReducedConnectedDim1OfGenus_iff (g : ℕ) {S : Scheme.{u}}
    (P : Obj S) :
    geometricallyReducedConnectedDim1OfGenus g S P ↔
      geometricallyReducedConnectedDim1 S P ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank g
          (higherDirectImageOne (hom P)) := sorry

/-- Membership in `geometricallyReducedConnectedDim1OfGenus g` is membership in
`geometricallyReducedConnectedDim1` together with membership in `ofGenus g`. -/
theorem geometricallyReducedConnectedDim1OfGenus_iff_ofGenus (g : ℕ)
    {S : Scheme.{u}} (P : Obj S) :
    geometricallyReducedConnectedDim1OfGenus g S P ↔
      geometricallyReducedConnectedDim1 S P ∧ ofGenus g S P := sorry

namespace geometricallyReducedConnectedDim1OfGenus

/-- Membership in `geometricallyReducedConnectedDim1OfGenus g` implies membership
in `geometricallyReducedConnectedDim1`. -/
theorem le (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    geometricallyReducedConnectedDim1OfGenus g S P →
      geometricallyReducedConnectedDim1 S P := sorry

end geometricallyReducedConnectedDim1OfGenus

/-- Membership in `geometricallyReducedConnectedDim1OfGenus g` implies membership
in `ofGenus g`. -/
theorem geometricallyReducedConnectedDim1OfGenus_le_ofGenus (g : ℕ)
    {S : Scheme.{u}} (P : Obj S) :
    geometricallyReducedConnectedDim1OfGenus g S P → ofGenus g S P := sorry

/-- A family of curves over a nonempty base lies in at most one of the
substacks `𝒞urves^{grc, 1}_g`. -/
theorem eq_of_mem_geometricallyReducedConnectedDim1OfGenus
    {S : Scheme.{u}} {P : Obj S} {g g' : ℕ} (hpt : Nonempty (base P).left)
    (hg : geometricallyReducedConnectedDim1OfGenus g S P)
    (hg' : geometricallyReducedConnectedDim1OfGenus g' S P) : g = g' := sorry

/-- The `geometricallyReducedConnectedDim1OfGenus` property of families of
curves is closed under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_geometricallyReducedConnectedDim1OfGenus
    (g : ℕ) (S : Scheme.{u}) :
    (geometricallyReducedConnectedDim1OfGenus g S).IsClosedUnderIsomorphisms := sorry

/-- Every family of curves with reduced, connected geometric fibres of dimension
one admits a pairwise disjoint clopen cover of its base by fixed-genus loci,
representing membership under every cartesian morphism of families. -/
theorem exists_geometricallyReducedConnectedDim1OfGenus_clopen_decomposition
    {S : Scheme.{u}} (P : Obj S) (h : geometricallyReducedConnectedDim1 S P) :
    ∃ U : ℕ → (base P).left.Opens,
      iSup U = ⊤ ∧
        Pairwise (fun g g' ↦ Disjoint (U g : Set (base P).left) (U g')) ∧
          (∀ g, IsClopen (U g : Set (base P).left)) ∧
            ∀ g, ∀ {Q : Obj S} (φ : Q ⟶ P),
              geometricallyReducedConnectedDim1OfGenus g S Q ↔
                Set.range (baseMap φ).left ⊆ U g := sorry

/-- A curve family has fixed genus `g` in the geometrically reduced connected
one-dimensional locus precisely when its geometric fibres are reduced, connected,
and one-dimensional, and its first structure-sheaf higher direct image is finite
locally free of rank `g`. -/
theorem geometricallyReducedConnectedDim1OfGenus_iff_geometricFibres
    {S : Scheme.{u}} (P : Obj S) (g : ℕ) :
    geometricallyReducedConnectedDim1OfGenus g S P ↔
      Hom.HasReducedGeometricFibres (hom P) ∧
        AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres (hom P) ∧
          (∀ ybar : GeometricPoint (ofOver (base P)),
              dimension (fieldFiber (hom P) ybar.toFieldValuedPoint) = 1) ∧
            SheafOfModules.IsFiniteLocallyFreeOfRank g
              (higherDirectImageOne (hom P)) := sorry

/-- A proper scheme of dimension at most one over a field lies in the
geometrically reduced connected genus-`g` locus precisely when it is geometrically
reduced, geometrically connected, one-dimensional, and has genus `g`. -/
theorem geometricallyReducedConnectedDim1OfGenus_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) :
    geometricallyReducedConnectedDim1OfGenus g (Spec (CommRingCat.of k))
        (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.geometricallyReduced X ∧
        GeometricallyConnected X.hom ∧
          ∃ (hdim1 : topologicalKrullDim X.left = 1)
            (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
            SchemeOverField.genus X hdim1 hΓ = g := sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
