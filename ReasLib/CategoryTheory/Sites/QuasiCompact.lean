module

public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Range
public import ReasLib.CategoryTheory.Sites.Family
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-compact objects of sites

This module records the chosen-cover and sieve-saturated notions of quasi-compactness for a
site, together with their fixed-target-family formulations.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe w u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Presieve

/-- The presieve formed by selecting a subfamily of the arrows already in `R`. -/
abbrev subfamily {U : C} (R : Presieve U) (T : Set R.uncurry) : Presieve U :=
  Presieve.ofArrows (fun i : T ↦ i.1.1.1) (fun i ↦ i.1.1.2)

end Presieve

namespace Precoverage

/-- The precoverage-level predicate underlying quasi-compactness for a chosen-cover site. -/
@[stacks 090H "precoverage owner"]
def QuasiCompactObject (K : Precoverage C) (U : C) : Prop :=
  ∀ (R : Presieve U), R ∈ K U →
    ∃ (S : Presieve U), S ∈ K U ∧
      ∃ (T : Set R.uncurry), T.Finite ∧ S.FactorsThru (R.subfamily T)

/-- A chosen-cover quasi-compact object admits refinements whose image in a given covering family
is finite. -/
theorem QuasiCompactObject.finite_image_refinement_of_family
    {K : Precoverage C} {U : C} (hU : K.QuasiCompactObject U)
    (𝒰 : SemiRepresentableFamily.Over.{w} U) (h𝒰 : 𝒰.toPresieve ∈ K U) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{max u v} U) (_ : 𝒱.toPresieve ∈ K U)
      (φ : SemiRepresentableFamily.Over.Hom 𝒱 𝒰), Set.Finite (Set.range φ.α) := sorry

/-- An object is quasi-compact for a precoverage exactly when every chosen covering family
in the canonical site-index universe admits a chosen covering refinement with finite
reindexing image. -/
theorem quasiCompactObject_iff_finite_image_refinement (K : Precoverage C) (U : C) :
    K.QuasiCompactObject U ↔
      ∀ (𝒰 : SemiRepresentableFamily.Over.{max u v} U), 𝒰.toPresieve ∈ K U →
        ∃ (𝒱 : SemiRepresentableFamily.Over.{max u v} U), 𝒱.toPresieve ∈ K U ∧
          ∃ (φ : SemiRepresentableFamily.Over.Hom 𝒱 𝒰),
            Set.Finite (Set.range φ.α) := sorry

end Precoverage

namespace Coverage

/-- An object of a site is quasi-compact when every chosen covering
family admits a covering refinement whose image in the original family is finite. -/
@[stacks 090H]
abbrev QuasiCompactObject (K : Coverage C) (U : C) : Prop :=
  K.toPrecoverage.QuasiCompactObject U

namespace QuasiCompactObject

/-- The fixed-target-family formulation of quasi-compactness for a chosen-cover site. -/
@[stacks 090H "fixed-target-family formulation"]
theorem finiteImageRefinement {K : Coverage C} {U : C}
    (hU : K.QuasiCompactObject U)
    (𝒰 : SemiRepresentableFamily.Over.{w} U) (h𝒰 : 𝒰.toPresieve ∈ K U) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{max u v} U) (_ : 𝒱.toPresieve ∈ K U)
      (φ : SemiRepresentableFamily.Over.Hom 𝒱 𝒰), Set.Finite (Set.range φ.α) := sorry

end QuasiCompactObject

end Coverage

namespace GrothendieckTopology

/-- An object is quasi-compact for a Grothendieck topology when every covering sieve contains a
finite family which is still covering. -/
def QuasiCompactObject (J : GrothendieckTopology C) (U : C) : Prop :=
  ∀ S : J.Cover U,
    ∃ (T : Set S.Arrow) (_ : T.Finite),
      Sieve.ofArrows (fun I : T ↦ I.1.Y) (fun I ↦ I.1.f) ∈ J U

/-- Sieve-saturated quasi-compactness is invariant under isomorphism of site objects. -/
instance quasiCompactObject_isClosedUnderIsomorphisms (J : GrothendieckTopology C) :
    CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms (J.QuasiCompactObject) := sorry

/-- A sieve-saturated quasi-compact object admits refinements whose image in a covering family is
finite. -/
theorem QuasiCompactObject.finite_image_refinement_of_family
    {J : GrothendieckTopology C} {U : C} (hU : QuasiCompactObject J U)
    (𝒰 : SemiRepresentableFamily.Over.{w} U) (h𝒰 : 𝒰.toSieve ∈ J U) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{w} U) (_ : 𝒱.toSieve ∈ J U) (φ : 𝒱 ⟶ 𝒰),
      Set.Finite (Set.range φ.α) := sorry

/-- The indexed-arrow formulation of sieve-saturated quasi-compactness. -/
theorem quasiCompactObject_finite_image_refinement_ofArrows
    {J : GrothendieckTopology C} {U : C} (hU : QuasiCompactObject J U)
    {ι : Type w} (Uᵢ : ι → C) (π : ∀ i : ι, Uᵢ i ⟶ U)
    (hcover : Sieve.ofArrows Uᵢ π ∈ J U) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{w} U) (_ : 𝒱.toSieve ∈ J U)
      (φ : 𝒱 ⟶ SemiRepresentableFamily.Over.ofArrows Uᵢ π),
      Set.Finite (Set.range φ.α) := sorry

end GrothendieckTopology

end CategoryTheory
