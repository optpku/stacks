/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.FilteredDerivedTotal
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.TotalHomology

/-!
# Naturality of Cartan--Eilenberg abutment comparisons

This leaf identifies the map induced by a Cartan--Eilenberg resolution map on mapped-total
cohomology with the canonical map on bounded-below total right-derived cohomology.  The same
statement is exposed for both standard filtered totals.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {K L M : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}
variable {N : CartanEilenbergResolution M}
variable (F : A ⥤ B) [F.Additive] [HasDerivedCategory.{w} B]
variable {E : Type u₃} [Category.{v₃} E]
variable (Q : HomotopyCategory.Plus A ⥤ E)
variable [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
variable [Functor.RightDerived.EverywhereDefined F.toBoundedBelowDerived
  (HomotopyCategory.Plus.quasiIso A)]

/-- The canonical map on bounded-below total right-derived cohomology induced by the base map
of a Cartan--Eilenberg resolution map. -/
@[stacks 015J "map on a Cartan-Eilenberg derived abutment"]
noncomputable abbrev derivedHomology
    (f : Map I J) (n : ℤ) :
    Functor.RightDerived.Bounded.cohomology F Q K n ⟶
      Functor.RightDerived.Bounded.cohomology F Q L n :=
  (DerivedCategory.Plus.homologyFunctor B n).map
    (Functor.RightDerived.Bounded.valueMap F.toBoundedBelowDerived Q f.base)

/-- The canonical derived-cohomology map preserves identity maps. -/
@[simp]
theorem derivedHomology_id (I : CartanEilenbergResolution K) (n : ℤ) :
    derivedHomology F Q (id I) n = 𝟙 _ := sorry

/-- The canonical derived-cohomology map preserves composition. -/
@[simp, reassoc]
theorem derivedHomology_comp (f : Map I J) (g : Map J N) (n : ℤ) :
    derivedHomology F Q (comp f g) n =
      derivedHomology F Q f n ≫ derivedHomology F Q g n := sorry

/-- Derived cohomology depends only on the bundled source map of a resolution map. -/
@[stacks 015J "independence of a Cartan-Eilenberg derived abutment from a lift"]
theorem derivedHomology_eq_of_base_eq
    (f g : Map I J) (hbase : f.base = g.base) (n : ℤ) :
    derivedHomology F Q f n = derivedHomology F Q g n := sorry

/-- The mapped-total cohomology comparison is natural in maps of Cartan--Eilenberg
resolutions. -/
@[stacks 015J "naturality of the Cartan-Eilenberg total abutment", reassoc]
theorem mappedTotalHomologyIso_naturality (f : Map I J) (n : ℤ) :
    mappedTotalHomology f F n ≫
        (MappedTotal.homologyIso J F Q n).hom =
      (MappedTotal.homologyIso I F Q n).hom ≫ derivedHomology F Q f n := sorry

/-- Inverse naturality of the mapped-total abutment comparison. -/
@[reassoc, stacks 015J "inverse naturality of the Cartan-Eilenberg total abutment"]
theorem mappedTotalHomologyIso_inv_naturality (f : Map I J) (n : ℤ) :
    derivedHomology F Q f n ≫ (MappedTotal.homologyIso J F Q n).inv =
      (MappedTotal.homologyIso I F Q n).inv ≫ mappedTotalHomology f F n := sorry

/-- Conjugating the derived abutment map by the mapped-total comparison recovers the
mapped-total map. -/
@[reassoc, stacks 015J "computation of the Cartan-Eilenberg total abutment"]
theorem mappedTotalHomologyIso_naturality_inv (f : Map I J) (n : ℤ) :
    (MappedTotal.homologyIso I F Q n).hom ≫ derivedHomology F Q f n ≫
        (MappedTotal.homologyIso J F Q n).inv =
      mappedTotalHomology f F n := sorry

/-- Conjugating the mapped-total abutment map by the inverse comparison recovers the
derived abutment map. -/
@[reassoc, stacks 015J "target-map computation for the Cartan-Eilenberg total abutment"]
theorem mappedTotalHomologyIso_target_map (f : Map I J) (n : ℤ) :
    (MappedTotal.homologyIso I F Q n).inv ≫ mappedTotalHomology f F n ≫
        (MappedTotal.homologyIso J F Q n).hom =
      derivedHomology F Q f n := sorry

/-- Two lifts of the same source map induce the same mapped-total cohomology map. -/
@[stacks 015J "independence of the Cartan-Eilenberg total abutment from a lift"]
theorem mappedTotalHomology_eq_of_base_eq
    (f g : Map I J) (hbase : f.base = g.base) (n : ℤ) :
    mappedTotalHomology f F n = mappedTotalHomology g F n := sorry

namespace First

/-- The first-filtered abutment comparison is natural in maps of Cartan--Eilenberg
resolutions. -/
@[stacks 015J "naturality of the first Cartan-Eilenberg filtered abutment", reassoc]
theorem filteredTotalHomologyIso_naturality (f : Map I J) (n : ℤ) :
    filteredTotalHomology f F n ≫
        (CartanEilenbergResolution.First.filteredTotalHomologyIso J F Q n).hom =
        (CartanEilenbergResolution.First.filteredTotalHomologyIso I F Q n).hom ≫
        derivedHomology F Q f n := sorry

/-- Inverse naturality of the first-filtered abutment comparison. -/
@[reassoc, stacks 015J "inverse naturality of the first Cartan-Eilenberg filtered abutment"]
theorem filteredTotalHomologyIso_inv_naturality (f : Map I J) (n : ℤ) :
    derivedHomology F Q f n ≫
        (CartanEilenbergResolution.First.filteredTotalHomologyIso J F Q n).inv =
      (CartanEilenbergResolution.First.filteredTotalHomologyIso I F Q n).inv ≫
        filteredTotalHomology f F n := sorry

/-- Conjugating the derived abutment map by the first-filtered comparison recovers the
first-filtered map. -/
@[reassoc, stacks 015J "computation of the first Cartan-Eilenberg filtered abutment"]
theorem filteredTotalHomologyIso_naturality_inv (f : Map I J) (n : ℤ) :
    (CartanEilenbergResolution.First.filteredTotalHomologyIso I F Q n).hom ≫
        derivedHomology F Q f n ≫
        (CartanEilenbergResolution.First.filteredTotalHomologyIso J F Q n).inv =
      filteredTotalHomology f F n := sorry

/-- Conjugating the first-filtered abutment map by the inverse comparison recovers the
derived abutment map. -/
@[reassoc, stacks 015J "target-map computation for the first Cartan-Eilenberg filtered abutment"]
theorem filteredTotalHomologyIso_target_map (f : Map I J) (n : ℤ) :
    (CartanEilenbergResolution.First.filteredTotalHomologyIso I F Q n).inv ≫
        filteredTotalHomology f F n ≫
        (CartanEilenbergResolution.First.filteredTotalHomologyIso J F Q n).hom =
      derivedHomology F Q f n := sorry

/-- Two lifts of the same source map induce the same first-filtered total cohomology map. -/
@[stacks 015J "independence of the first Cartan-Eilenberg filtered abutment from a lift"]
theorem filteredTotalHomology_eq_of_base_eq
    (f g : Map I J) (hbase : f.base = g.base) (n : ℤ) :
    filteredTotalHomology f F n = filteredTotalHomology g F n := sorry

end First

namespace Second

/-- The second-filtered abutment comparison is natural in maps of Cartan--Eilenberg
resolutions. -/
@[stacks 015J "naturality of the second Cartan-Eilenberg filtered abutment", reassoc]
theorem filteredTotalHomologyIso_naturality (f : Map I J) (n : ℤ) :
    filteredTotalHomology f F n ≫
        (CartanEilenbergResolution.Second.filteredTotalHomologyIso J F Q n).hom =
        (CartanEilenbergResolution.Second.filteredTotalHomologyIso I F Q n).hom ≫
        derivedHomology F Q f n := sorry

/-- Inverse naturality of the second-filtered abutment comparison. -/
@[reassoc, stacks 015J "inverse naturality of the second Cartan-Eilenberg filtered abutment"]
theorem filteredTotalHomologyIso_inv_naturality (f : Map I J) (n : ℤ) :
    derivedHomology F Q f n ≫
        (CartanEilenbergResolution.Second.filteredTotalHomologyIso J F Q n).inv =
      (CartanEilenbergResolution.Second.filteredTotalHomologyIso I F Q n).inv ≫
        filteredTotalHomology f F n := sorry

/-- Conjugating the derived abutment map by the second-filtered comparison recovers the
second-filtered map. -/
@[reassoc, stacks 015J "computation of the second Cartan-Eilenberg filtered abutment"]
theorem filteredTotalHomologyIso_naturality_inv (f : Map I J) (n : ℤ) :
    (CartanEilenbergResolution.Second.filteredTotalHomologyIso I F Q n).hom ≫
        derivedHomology F Q f n ≫
        (CartanEilenbergResolution.Second.filteredTotalHomologyIso J F Q n).inv =
      filteredTotalHomology f F n := sorry

/-- Conjugating the second-filtered abutment map by the inverse comparison recovers the
derived abutment map. -/
@[reassoc, stacks 015J "target-map computation for the second Cartan-Eilenberg filtered abutment"]
theorem filteredTotalHomologyIso_target_map (f : Map I J) (n : ℤ) :
    (CartanEilenbergResolution.Second.filteredTotalHomologyIso I F Q n).inv ≫
        filteredTotalHomology f F n ≫
        (CartanEilenbergResolution.Second.filteredTotalHomologyIso J F Q n).hom =
      derivedHomology F Q f n := sorry

/-- Two lifts of the same source map induce the same second-filtered total cohomology map. -/
@[stacks 015J "independence of the second Cartan-Eilenberg filtered abutment from a lift"]
theorem filteredTotalHomology_eq_of_base_eq
    (f g : Map I J) (hbase : f.base = g.base) (n : ℤ) :
    filteredTotalHomology f F n = filteredTotalHomology g F n := sorry

end Second

end CochainComplex.CartanEilenbergResolution.Map
