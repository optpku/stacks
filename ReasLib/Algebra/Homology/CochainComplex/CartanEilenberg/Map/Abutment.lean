/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
    derivedHomology F Q (id I) n = 𝟙 _ := by
  exact (Functor.RightDerived.Bounded.cohomologyFunctor F Q n).map_id K

/-- The canonical derived-cohomology map preserves composition. -/
@[simp, reassoc]
theorem derivedHomology_comp (f : Map I J) (g : Map J N) (n : ℤ) :
    derivedHomology F Q (comp f g) n =
      derivedHomology F Q f n ≫ derivedHomology F Q g n := by
  exact (Functor.RightDerived.Bounded.cohomologyFunctor F Q n).map_comp f.base g.base

/-- Derived cohomology depends only on the bundled source map of a resolution map. -/
@[stacks 015J "independence of a Cartan-Eilenberg derived abutment from a lift"]
theorem derivedHomology_eq_of_base_eq
    (f g : Map I J) (hbase : f.base = g.base) (n : ℤ) :
    derivedHomology F Q f n = derivedHomology F Q g n := by
  exact congrArg (Functor.RightDerived.Bounded.cohomologyFunctor F Q n).map hbase

/-- The mapped-total cohomology comparison is natural in maps of Cartan--Eilenberg
resolutions. -/
@[stacks 015J "naturality of the Cartan-Eilenberg total abutment", reassoc]
theorem mappedTotalHomologyIso_naturality (f : Map I J) (n : ℤ) :
    mappedTotalHomology f F n ≫
        (MappedTotal.homologyIso J F Q n).hom =
      (MappedTotal.homologyIso I F Q n).hom ≫ derivedHomology F Q f n := by
  let H := HomologicalComplex.homologyFunctor B (up ℤ) n
  let D := DerivedCategory.Plus.homologyFunctor B n
  have htotal : CommSq (mappedTotal f F) (MappedTotal.iso I F).hom
      (MappedTotal.iso J F).hom ((F.mapHomologicalComplex (up ℤ)).map (total f)) :=
    ⟨HomologicalComplex₂.Total.Map.Comparison.naturality F (up ℤ) f.hom⟩
  have hhomology : CommSq (H.map ((F.mapHomologicalComplex (up ℤ)).map (total f)))
      (Functor.Homotopy.Plus.Homology.homologyIso F (Total.toPlus I) n).hom
      (Functor.Homotopy.Plus.Homology.homologyIso F (Total.toPlus J) n).hom
      (D.map (F.toBoundedBelowDerived.map
        ((HomotopyCategory.Plus.quotient A).map (totalPlus f)))) :=
    ⟨Functor.Homotopy.Plus.Homology.homologyIso.hom_naturality F (totalPlus f) n⟩
  have haug : Total.augmentationPlus I ≫ totalPlus f =
      f.base ≫ Total.augmentationPlus J := by
    apply (CochainComplex.Plus.ι A).map_injective
    exact totalAugmentation_naturality f
  have haugHomotopy : Total.augmentationHomotopy I ≫
      (HomotopyCategory.Plus.quotient A).map (totalPlus f) =
      (HomotopyCategory.Plus.quotient A).map f.base ≫ Total.augmentationHomotopy J := by
    calc
      _ = (HomotopyCategory.Plus.quotient A).map
          (Total.augmentationPlus I ≫ totalPlus f) :=
        ((HomotopyCategory.Plus.quotient A).map_comp _ _).symm
      _ = (HomotopyCategory.Plus.quotient A).map
          (f.base ≫ Total.augmentationPlus J) :=
        congrArg (HomotopyCategory.Plus.quotient A).map haug
      _ = _ := (HomotopyCategory.Plus.quotient A).map_comp _ _
  have hderived : CommSq
      (F.toBoundedBelowDerived.map ((HomotopyCategory.Plus.quotient A).map (totalPlus f)))
      (Total.rightDerivedIso I F.toBoundedBelowDerived Q).hom
      (Total.rightDerivedIso J F.toBoundedBelowDerived Q).hom
      (Functor.RightDerived.Bounded.valueMap F.toBoundedBelowDerived Q f.base) :=
    ⟨Functor.RightDerived.ComputesAt.replacementIso_hom_naturality
      F.toBoundedBelowDerived (HomotopyCategory.Plus.quasiIso A) Q
      (Total.augmentationHomotopy I) (Total.augmentationHomotopy_quasiIso I)
      (Total.computesRightDerivedAt I F.toBoundedBelowDerived)
      (Total.augmentationHomotopy J) (Total.augmentationHomotopy_quasiIso J)
      (Total.computesRightDerivedAt J F.toBoundedBelowDerived)
      ((HomotopyCategory.Plus.quotient A).map f.base)
      ((HomotopyCategory.Plus.quotient A).map (totalPlus f)) haugHomotopy⟩
  have h := (((H.map_commSq htotal).vert_comp hhomology).vert_comp
    (D.map_commSq hderived)).w
  simp only [Category.assoc] at h
  simp only [MappedTotal.homologyIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  exact h

/-- Inverse naturality of the mapped-total abutment comparison. -/
@[reassoc, stacks 015J "inverse naturality of the Cartan-Eilenberg total abutment"]
theorem mappedTotalHomologyIso_inv_naturality (f : Map I J) (n : ℤ) :
    derivedHomology F Q f n ≫ (MappedTotal.homologyIso J F Q n).inv =
      (MappedTotal.homologyIso I F Q n).inv ≫ mappedTotalHomology f F n := by
  apply (Iso.eq_inv_comp (MappedTotal.homologyIso I F Q n)).2
  rw [← mappedTotalHomologyIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-- Conjugating the derived abutment map by the mapped-total comparison recovers the
mapped-total map. -/
@[reassoc, stacks 015J "computation of the Cartan-Eilenberg total abutment"]
theorem mappedTotalHomologyIso_naturality_inv (f : Map I J) (n : ℤ) :
    (MappedTotal.homologyIso I F Q n).hom ≫ derivedHomology F Q f n ≫
        (MappedTotal.homologyIso J F Q n).inv =
      mappedTotalHomology f F n := by
  rw [← mappedTotalHomologyIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-- Conjugating the mapped-total abutment map by the inverse comparison recovers the
derived abutment map. -/
@[reassoc, stacks 015J "target-map computation for the Cartan-Eilenberg total abutment"]
theorem mappedTotalHomologyIso_target_map (f : Map I J) (n : ℤ) :
    (MappedTotal.homologyIso I F Q n).inv ≫ mappedTotalHomology f F n ≫
        (MappedTotal.homologyIso J F Q n).hom =
      derivedHomology F Q f n := by
  rw [mappedTotalHomologyIso_naturality, Iso.inv_hom_id_assoc]

/-- Two lifts of the same source map induce the same mapped-total cohomology map. -/
@[stacks 015J "independence of the Cartan-Eilenberg total abutment from a lift"]
theorem mappedTotalHomology_eq_of_base_eq
    (f g : Map I J) (hbase : f.base = g.base) (n : ℤ) :
    mappedTotalHomology f F n = mappedTotalHomology g F n := by
  let Q₀ := (HomotopyCategory.Plus.quasiIso A).Q
  rw [← mappedTotalHomologyIso_naturality_inv F Q₀ f n,
    ← mappedTotalHomologyIso_naturality_inv F Q₀ g n,
    derivedHomology_eq_of_base_eq F Q₀ f g hbase n]

namespace First

/-- The first-filtered abutment comparison is natural in maps of Cartan--Eilenberg
resolutions. -/
@[stacks 015J "naturality of the first Cartan-Eilenberg filtered abutment", reassoc]
theorem filteredTotalHomologyIso_naturality (f : Map I J) (n : ℤ) :
    filteredTotalHomology f F n ≫
        (CartanEilenbergResolution.First.filteredTotalHomologyIso J F Q n).hom =
        (CartanEilenbergResolution.First.filteredTotalHomologyIso I F Q n).hom ≫
        derivedHomology F Q f n := by
  let H := HomologicalComplex.homologyFunctor B (up ℤ) n
  have hI : H.map
      (eqToIso (HomologicalComplex₂.First.Filtration.total_underlying (I.mapBicomplex F))).hom =
      𝟙 _ := by
    rw [eqToIso.hom, eqToHom_map]
    exact eqToHom_refl _ _
  have hJ : H.map
      (eqToIso (HomologicalComplex₂.First.Filtration.total_underlying (J.mapBicomplex F))).hom =
      𝟙 _ := by
    rw [eqToIso.hom, eqToHom_map]
    exact eqToHom_refl _ _
  simp only [CartanEilenbergResolution.First.filteredTotalHomologyIso, Iso.trans_hom,
    Functor.mapIso_hom]
  erw [hI, hJ]
  erw [Category.id_comp, Category.id_comp]
  rw [filteredTotalHomology_eq_mapped]
  exact mappedTotalHomologyIso_naturality F Q f n

/-- Inverse naturality of the first-filtered abutment comparison. -/
@[reassoc, stacks 015J "inverse naturality of the first Cartan-Eilenberg filtered abutment"]
theorem filteredTotalHomologyIso_inv_naturality (f : Map I J) (n : ℤ) :
    derivedHomology F Q f n ≫
        (CartanEilenbergResolution.First.filteredTotalHomologyIso J F Q n).inv =
      (CartanEilenbergResolution.First.filteredTotalHomologyIso I F Q n).inv ≫
        filteredTotalHomology f F n := by
  apply (Iso.eq_inv_comp (CartanEilenbergResolution.First.filteredTotalHomologyIso I F Q n)).2
  rw [← filteredTotalHomologyIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-- Conjugating the derived abutment map by the first-filtered comparison recovers the
first-filtered map. -/
@[reassoc, stacks 015J "computation of the first Cartan-Eilenberg filtered abutment"]
theorem filteredTotalHomologyIso_naturality_inv (f : Map I J) (n : ℤ) :
    (CartanEilenbergResolution.First.filteredTotalHomologyIso I F Q n).hom ≫
        derivedHomology F Q f n ≫
        (CartanEilenbergResolution.First.filteredTotalHomologyIso J F Q n).inv =
      filteredTotalHomology f F n := by
  rw [← filteredTotalHomologyIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-- Conjugating the first-filtered abutment map by the inverse comparison recovers the
derived abutment map. -/
@[reassoc, stacks 015J "target-map computation for the first Cartan-Eilenberg filtered abutment"]
theorem filteredTotalHomologyIso_target_map (f : Map I J) (n : ℤ) :
    (CartanEilenbergResolution.First.filteredTotalHomologyIso I F Q n).inv ≫
        filteredTotalHomology f F n ≫
        (CartanEilenbergResolution.First.filteredTotalHomologyIso J F Q n).hom =
      derivedHomology F Q f n := by
  rw [filteredTotalHomologyIso_naturality, Iso.inv_hom_id_assoc]

/-- Two lifts of the same source map induce the same first-filtered total cohomology map. -/
@[stacks 015J "independence of the first Cartan-Eilenberg filtered abutment from a lift"]
theorem filteredTotalHomology_eq_of_base_eq
    (f g : Map I J) (hbase : f.base = g.base) (n : ℤ) :
    filteredTotalHomology f F n = filteredTotalHomology g F n := by
  rw [filteredTotalHomology_eq_mapped, filteredTotalHomology_eq_mapped]
  exact mappedTotalHomology_eq_of_base_eq F f g hbase n

end First

namespace Second

/-- The second-filtered abutment comparison is natural in maps of Cartan--Eilenberg
resolutions. -/
@[stacks 015J "naturality of the second Cartan-Eilenberg filtered abutment", reassoc]
theorem filteredTotalHomologyIso_naturality (f : Map I J) (n : ℤ) :
    filteredTotalHomology f F n ≫
        (CartanEilenbergResolution.Second.filteredTotalHomologyIso J F Q n).hom =
        (CartanEilenbergResolution.Second.filteredTotalHomologyIso I F Q n).hom ≫
        derivedHomology F Q f n := by
  let H := HomologicalComplex.homologyFunctor B (up ℤ) n
  have hI : H.map
      (eqToIso (HomologicalComplex₂.Second.Filtration.total_underlying (I.mapBicomplex F))).hom =
      𝟙 _ := by
    rw [eqToIso.hom, eqToHom_map]
    exact eqToHom_refl _ _
  have hJ : H.map
      (eqToIso (HomologicalComplex₂.Second.Filtration.total_underlying (J.mapBicomplex F))).hom =
      𝟙 _ := by
    rw [eqToIso.hom, eqToHom_map]
    exact eqToHom_refl _ _
  simp only [CartanEilenbergResolution.Second.filteredTotalHomologyIso, Iso.trans_hom,
    Functor.mapIso_hom]
  erw [hI, hJ]
  erw [Category.id_comp, Category.id_comp]
  rw [filteredTotalHomology_eq_mapped]
  exact mappedTotalHomologyIso_naturality F Q f n

/-- Inverse naturality of the second-filtered abutment comparison. -/
@[reassoc, stacks 015J "inverse naturality of the second Cartan-Eilenberg filtered abutment"]
theorem filteredTotalHomologyIso_inv_naturality (f : Map I J) (n : ℤ) :
    derivedHomology F Q f n ≫
        (CartanEilenbergResolution.Second.filteredTotalHomologyIso J F Q n).inv =
      (CartanEilenbergResolution.Second.filteredTotalHomologyIso I F Q n).inv ≫
        filteredTotalHomology f F n := by
  apply (Iso.eq_inv_comp (CartanEilenbergResolution.Second.filteredTotalHomologyIso I F Q n)).2
  rw [← filteredTotalHomologyIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-- Conjugating the derived abutment map by the second-filtered comparison recovers the
second-filtered map. -/
@[reassoc, stacks 015J "computation of the second Cartan-Eilenberg filtered abutment"]
theorem filteredTotalHomologyIso_naturality_inv (f : Map I J) (n : ℤ) :
    (CartanEilenbergResolution.Second.filteredTotalHomologyIso I F Q n).hom ≫
        derivedHomology F Q f n ≫
        (CartanEilenbergResolution.Second.filteredTotalHomologyIso J F Q n).inv =
      filteredTotalHomology f F n := by
  rw [← filteredTotalHomologyIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-- Conjugating the second-filtered abutment map by the inverse comparison recovers the
derived abutment map. -/
@[reassoc, stacks 015J "target-map computation for the second Cartan-Eilenberg filtered abutment"]
theorem filteredTotalHomologyIso_target_map (f : Map I J) (n : ℤ) :
    (CartanEilenbergResolution.Second.filteredTotalHomologyIso I F Q n).inv ≫
        filteredTotalHomology f F n ≫
        (CartanEilenbergResolution.Second.filteredTotalHomologyIso J F Q n).hom =
      derivedHomology F Q f n := by
  rw [filteredTotalHomologyIso_naturality, Iso.inv_hom_id_assoc]

/-- Two lifts of the same source map induce the same second-filtered total cohomology map. -/
@[stacks 015J "independence of the second Cartan-Eilenberg filtered abutment from a lift"]
theorem filteredTotalHomology_eq_of_base_eq
    (f g : Map I J) (hbase : f.base = g.base) (n : ℤ) :
    filteredTotalHomology f F n = filteredTotalHomology g F n := by
  rw [filteredTotalHomology_eq_mapped, filteredTotalHomology_eq_mapped]
  exact mappedTotalHomology_eq_of_base_eq F f g hbase n

end Second

end CochainComplex.CartanEilenbergResolution.Map
