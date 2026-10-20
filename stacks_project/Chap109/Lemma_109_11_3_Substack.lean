/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.Topology.Clopen
public import stacks_project.Chap109.Lemma_109_11_1_Substack
public import stacks_project.Chap109.Lemma_109_9_4_Substack

/-!
# The object property of geometrically reduced connected curves of a given genus

`𝒞urves^{grc, 1}_g` is the full subcategory of families of curves in
`𝒞urves^{grc, 1}` for which `R¹ f_* 𝒪_X` is finite locally free of rank
`g`. Membership is the source-facing packaging of a classifying morphism
factoring through that open-and-closed substack. The coproduct decomposition
of the parent locus is a pairwise-disjoint clopen cover of the base, with
possibly empty pieces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The object property of families of curves with reduced, connected geometric
fibres of dimension `1` and `R¹ f_* 𝒪_X` finite locally free of rank `g`,
corresponding to the open-and-closed substack `𝒞urves^{grc, 1}_g`. -/
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
          (higherDirectImageOne (hom P)) :=
  sorry

/-- Membership in `geometricallyReducedConnectedDim1OfGenus g` is membership in
`geometricallyReducedConnectedDim1` together with membership in `ofGenus g`. -/
theorem geometricallyReducedConnectedDim1OfGenus_iff_ofGenus (g : ℕ)
    {S : Scheme.{u}} (P : Obj S) :
    geometricallyReducedConnectedDim1OfGenus g S P ↔
      geometricallyReducedConnectedDim1 S P ∧ ofGenus g S P :=
  sorry

namespace geometricallyReducedConnectedDim1OfGenus

/-- Membership in `geometricallyReducedConnectedDim1OfGenus g` implies membership
in `geometricallyReducedConnectedDim1`. -/
theorem le (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    geometricallyReducedConnectedDim1OfGenus g S P →
      geometricallyReducedConnectedDim1 S P :=
  sorry

end geometricallyReducedConnectedDim1OfGenus

/-- Membership in `geometricallyReducedConnectedDim1OfGenus g` implies membership
in `ofGenus g`. -/
theorem geometricallyReducedConnectedDim1OfGenus_le_ofGenus (g : ℕ)
    {S : Scheme.{u}} (P : Obj S) :
    geometricallyReducedConnectedDim1OfGenus g S P → ofGenus g S P :=
  sorry

/-- A family of curves over a nonempty base lies in at most one of the
substacks `𝒞urves^{grc, 1}_g`. -/
theorem eq_of_mem_geometricallyReducedConnectedDim1OfGenus
    {S : Scheme.{u}} {P : Obj S} {g g' : ℕ} (hpt : Nonempty (base P).left)
    (hg : geometricallyReducedConnectedDim1OfGenus g S P)
    (hg' : geometricallyReducedConnectedDim1OfGenus g' S P) : g = g' :=
  sorry

/-- The open `U` of the base of a family of curves, as a scheme over `S`. -/
def baseOpen {S : Scheme.{u}} (P : Obj S) (U : (base P).left.Opens) : Over S :=
  Over.mk (U.ι ≫ (base P).hom)

/-- The structure morphism of `baseOpen P U` is `U.ι ≫ (base P).hom`. -/
theorem baseOpen_hom {S : Scheme.{u}} (P : Obj S) (U : (base P).left.Opens) :
    (baseOpen P U).hom = U.ι ≫ (base P).hom :=
  sorry

/-- The open immersion of `U` as a morphism of bases over `S`. -/
def baseOpenι {S : Scheme.{u}} (P : Obj S) (U : (base P).left.Opens) :
    baseOpen P U ⟶ base P :=
  Over.homMk U.ι

/-- The underlying scheme morphism of `baseOpenι P U` is `U.ι`. -/
theorem baseOpenι_left {S : Scheme.{u}} (P : Obj S) (U : (base P).left.Opens) :
    (baseOpenι P U).left = U.ι :=
  sorry

/-- Base change of an fp-flat-proper family of curves along an open of the base
remains fp-flat-proper. -/
instance instFpFlatProper_pullback_snd_baseOpenι {S : Scheme.{u}} (P : Obj S)
    (U : (base P).left.Opens) :
    FpFlatProper (pullback.snd (hom P) (ofOverMap (baseOpenι P U))) :=
  sorry

/-- Base change of a family of curves of relative dimension at most `1` along an
open of the base remains of relative dimension at most `1`. -/
instance instRelativeDimensionLE_pullback_snd_baseOpenι {S : Scheme.{u}}
    (P : Obj S) (U : (base P).left.Opens) :
    RelativeDimensionLE (pullback.snd (hom P) (ofOverMap (baseOpenι P U))) 1 :=
  sorry

/-- The base change of a family of curves to an open of its base. -/
def baseChangeToOpen {S : Scheme.{u}} (P : Obj S) (U : (base P).left.Opens) :
    Obj S :=
  mk (pullback.snd (hom P) (ofOverMap (baseOpenι P U)))

/-- The structure morphism of `baseChangeToOpen P U` is the second projection of
the pullback of `hom P` along `ofOverMap (baseOpenι P U)`. -/
theorem baseChangeToOpen_hom {S : Scheme.{u}} (P : Obj S)
    (U : (base P).left.Opens) :
    hom (baseChangeToOpen P U) =
      pullback.snd (hom P) (ofOverMap (baseOpenι P U)) :=
  sorry

/-- The base of `baseChangeToOpen P U` is `baseOpen P U`. -/
theorem baseChangeToOpen_base {S : Scheme.{u}} (P : Obj S)
    (U : (base P).left.Opens) :
    base (baseChangeToOpen P U) = baseOpen P U :=
  sorry

namespace geometricallyReducedConnectedDim1

/-- A family of curves lies in `geometricallyReducedConnectedDim1` if and only
if its base admits a pairwise-disjoint clopen cover `(U_g)_{g : ℕ}`, with
pieces possibly empty, such that the base change to each `U_g` lies in
`geometricallyReducedConnectedDim1OfGenus g`. -/
theorem mem_iff_clopenCover {S : Scheme.{u}} (P : Obj S) :
    geometricallyReducedConnectedDim1 S P ↔
      ∃ U : ℕ → (base P).left.Opens,
        iSup U = ⊤ ∧
          Pairwise (fun g g' ↦
              Disjoint (U g : Set (base P).left) (U g')) ∧
            (∀ g, IsClopen (U g : Set (base P).left)) ∧
              ∀ g, geometricallyReducedConnectedDim1OfGenus g S
                (baseChangeToOpen P (U g)) :=
  sorry

end geometricallyReducedConnectedDim1

/-- The `geometricallyReducedConnectedDim1OfGenus` property of families of
curves is closed under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_geometricallyReducedConnectedDim1OfGenus
    (g : ℕ) (S : Scheme.{u}) :
    (geometricallyReducedConnectedDim1OfGenus g S).IsClosedUnderIsomorphisms :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
