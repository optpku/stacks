module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Basic

/-!
# Morphisms of Grothendieck Spectral Sequences

This leaf records the maps induced by a morphism of bounded-below derived objects.  Compatibility
with the filtered-complex association is separated from the page-two and abutment squares, so
each part can be reused independently.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB wC v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Grothendieck

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Abelian A] [Abelian B] [Abelian C]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable [HasDerivedCategory.{wC} C] [HasInjectiveResolutions B]

/-- The morphism on the `(p, q)` page-two targets induced by a morphism of derived objects. -/
@[stacks 015N "Grothendieck spectral-sequence naturality"]
noncomputable abbrev pageTwoMap
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    {X Y : DerivedCategory.Plus A} (f : X ⟶ Y) (p : ℕ) (q : ℤ) :
    pageTwo G RF X p q ⟶ pageTwo G RF Y p q :=
  (pageTwoFunctor G RF p q).map f

/-- The morphism on degree-`n` abutment targets induced by a morphism of derived objects. -/
@[stacks 015N "Grothendieck spectral-sequence naturality"]
noncomputable abbrev abutmentMap
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C)
    {X Y : DerivedCategory.Plus A} (f : X ⟶ Y) (n : ℤ) :
    abutment RGF X n ⟶ abutment RGF Y n :=
  (abutmentFunctor RGF n).map f

/-- The page-two target map of an identity morphism is the identity. -/
@[simp, stacks 015N "Grothendieck spectral-sequence naturality"]
theorem pageTwoMap_id
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (X : DerivedCategory.Plus A) (p : ℕ) (q : ℤ) :
    pageTwoMap G RF (𝟙 X) p q = 𝟙 (pageTwo G RF X p q) := sorry

/-- Page-two target maps compose with the derived-object morphisms. -/
@[simp, reassoc, stacks 015N "Grothendieck spectral-sequence naturality"]
theorem pageTwoMap_comp
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    {X Y Z : DerivedCategory.Plus A} (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℕ) (q : ℤ) :
    pageTwoMap G RF (f ≫ g) p q =
      pageTwoMap G RF f p q ≫ pageTwoMap G RF g p q := sorry

/-- The abutment target map of an identity morphism is the identity. -/
@[simp, stacks 015N "Grothendieck spectral-sequence naturality"]
theorem abutmentMap_id
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C)
    (X : DerivedCategory.Plus A) (n : ℤ) :
    abutmentMap RGF (𝟙 X) n = 𝟙 (abutment RGF X n) := sorry

/-- Abutment target maps compose with the derived-object morphisms. -/
@[simp, reassoc, stacks 015N "Grothendieck spectral-sequence naturality"]
theorem abutmentMap_comp
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C)
    {X Y Z : DerivedCategory.Plus A} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℤ) :
    abutmentMap RGF (f ≫ g) n = abutmentMap RGF f n ≫ abutmentMap RGF g n := sorry

namespace SpectralSequence

/-- A morphism between two Grothendieck spectral-sequence realizations over `f`.  It includes
the induced-map condition for the chosen filtered-complex associations and the expected maps on
the second page and abutment. -/
@[stacks 015N "functoriality of the Grothendieck spectral sequence"]
structure Map
    {G : B ⥤ C} [G.Additive] {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}
    {X Y : DerivedCategory.Plus A} (f : X ⟶ Y)
    (S : SpectralSequence G RF RGF X) (T : SpectralSequence G RF RGF Y)
    extends toWithAbutmentMap :
      FilteredComplex.SpectralSequence.Realization.WithAbutment.Map
        (abutmentFunctor RGF) f S.toWithAbutment T.toWithAbutment where
  /-- Naturality of the chosen second-page comparisons. -/
  pageTwoSq : ∀ (p : ℕ) (q : ℤ),
    CommSq ((sequenceMap.hom 2).f (Int.ofNat p, q))
      (S.pageTwoIso p q).hom (T.pageTwoIso p q).hom (pageTwoMap G RF f p q)

namespace Map

/-- The generic filtered spectral-sequence realization map underlying a Grothendieck map. -/
@[stacks 015N "underlying Grothendieck spectral-sequence realization map"]
abbrev toMap
    {G : B ⥤ C} [G.Additive]
    {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}
    {X Y : DerivedCategory.Plus A} {f : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (m : Map f S T) :
    FilteredComplex.SpectralSequence.Realization.Map S.toRealization T.toRealization :=
  m.toWithAbutmentMap.toRealizationMap

/-- The association morphism underlying a Grothendieck spectral-sequence map. -/
@[stacks 015N "association morphism of a Grothendieck spectral-sequence map"]
def toAssociationHom
    {G : B ⥤ C} [G.Additive]
    {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}
    {X Y : DerivedCategory.Plus A} {f : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (m : Map f S T) :
    FilteredComplex.Association.Hom S.association T.association m.filteredMap :=
  FilteredComplex.SpectralSequence.Realization.WithAbutment.Map.toAssociationHom
    (abutmentFunctor RGF) m.toWithAbutmentMap

/-- The association morphism has the spectral-sequence component of the Grothendieck map. -/
@[simp, stacks 015N "association morphism of a Grothendieck spectral-sequence map"]
theorem toAssociationHom_hom
    {G : B ⥤ C} [G.Additive]
    {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}
    {X Y : DerivedCategory.Plus A} {f : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (m : Map f S T) : (toAssociationHom m).hom = m.sequenceMap := sorry

/-- Two morphisms over the same derived-category arrow are equal when their filtered-complex and
spectral-sequence components agree.  The remaining fields are proposition-valued compatibility
proofs and are therefore irrelevant to extensional equality. -/
@[ext, stacks 015N "extensionality of Grothendieck spectral-sequence maps"]
theorem ext
    {G : B ⥤ C} [G.Additive]
    {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}
    {X Y : DerivedCategory.Plus A} {f : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    {m n : Map f S T}
    (h_filtered : m.filteredMap = n.filteredMap)
    (h_sequence : m.sequenceMap = n.sequenceMap) : m = n := sorry

/-- A Grothendieck spectral-sequence map is determined by its filtered-complex component.  The
induced spectral-sequence map is unique, and the page-two and abutment fields are propositions. -/
@[stacks 015N "extensionality of Grothendieck spectral-sequence maps"]
theorem ext_filteredMap
    {G : B ⥤ C} [G.Additive]
    {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}
    {X Y : DerivedCategory.Plus A} {f : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    {m n : Map f S T}
    (h_filtered : m.filteredMap = n.filteredMap) : m = n := sorry

/-- Equation form of naturality on the second page. -/
@[reassoc, stacks 015N "Grothendieck spectral-sequence page-two naturality"]
theorem pageTwo_hom
    {G : B ⥤ C} [G.Additive] {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}
    {X Y : DerivedCategory.Plus A} {f : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (m : Map f S T) (p : ℕ) (q : ℤ) :
    (m.sequenceMap.hom 2).f (Int.ofNat p, q) ≫ (T.pageTwoIso p q).hom =
      (S.pageTwoIso p q).hom ≫ pageTwoMap G RF f p q := sorry

/-- Equation form of naturality on the abutment. -/
@[reassoc, stacks 015N "Grothendieck spectral-sequence abutment naturality"]
theorem abutment_hom
    {G : B ⥤ C} [G.Additive] {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}
    {X Y : DerivedCategory.Plus A} {f : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (m : Map f S T) (n : ℤ) :
    HomologicalComplex.homologyMap (S.filtered.underlyingMap m.filteredMap) n ≫
        (T.abutmentIso n).hom =
      (S.abutmentIso n).hom ≫ abutmentMap RGF f n := sorry

/-- Inverse naturality on the second page of a Grothendieck spectral-sequence map. -/
@[reassoc, stacks 015N "inverse Grothendieck spectral-sequence page-two naturality"]
theorem pageTwo_inv_naturality
    {G : B ⥤ C} [G.Additive] {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}
    {X Y : DerivedCategory.Plus A} {f : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (m : Map f S T) (p : ℕ) (q : ℤ) :
    pageTwoMap G RF f p q ≫ (T.pageTwoIso p q).inv =
      (S.pageTwoIso p q).inv ≫ (m.sequenceMap.hom 2).f (Int.ofNat p, q) := sorry

/-- Inverse naturality on the abutment of a Grothendieck spectral-sequence map. -/
@[reassoc, stacks 015N "inverse Grothendieck spectral-sequence abutment naturality"]
theorem abutment_inv_naturality
    {G : B ⥤ C} [G.Additive] {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}
    {X Y : DerivedCategory.Plus A} {f : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (m : Map f S T) (n : ℤ) :
    abutmentMap RGF f n ≫ (T.abutmentIso n).inv =
      (S.abutmentIso n).inv ≫
        HomologicalComplex.homologyMap (S.filtered.underlyingMap m.filteredMap) n := sorry

/-- Conjugating the page-two target map by the selected comparisons recovers the underlying
second-page component of a Grothendieck spectral-sequence map. -/
@[reassoc, stacks 015N "computation of the Grothendieck page-two map"]
theorem pageTwo_naturality_inv
    {G : B ⥤ C} [G.Additive] {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}
    {X Y : DerivedCategory.Plus A} {f : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (m : Map f S T) (p : ℕ) (q : ℤ) :
    (S.pageTwoIso p q).hom ≫ pageTwoMap G RF f p q ≫ (T.pageTwoIso p q).inv =
      (m.sequenceMap.hom 2).f (Int.ofNat p, q) := sorry

/-- Conjugating the underlying second-page component by the inverse selected comparisons
recovers the page-two target map. -/
@[reassoc, stacks 015N "target-map computation for the Grothendieck page-two comparison"]
theorem pageTwo_target_map
    {G : B ⥤ C} [G.Additive] {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}
    {X Y : DerivedCategory.Plus A} {f : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (m : Map f S T) (p : ℕ) (q : ℤ) :
    (S.pageTwoIso p q).inv ≫ (m.sequenceMap.hom 2).f (Int.ofNat p, q) ≫
        (T.pageTwoIso p q).hom =
      pageTwoMap G RF f p q := sorry

/-- Conjugating the target abutment map by the selected comparisons recovers the map on
cohomology of the underlying filtered complexes. -/
@[reassoc, stacks 015N "computation of the Grothendieck abutment map"]
theorem abutment_naturality_inv
    {G : B ⥤ C} [G.Additive] {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}
    {X Y : DerivedCategory.Plus A} {f : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (m : Map f S T) (n : ℤ) :
    (S.abutmentIso n).hom ≫ abutmentMap RGF f n ≫ (T.abutmentIso n).inv =
      HomologicalComplex.homologyMap (S.filtered.underlyingMap m.filteredMap) n := sorry

/-- Conjugating the underlying abutment component by the inverse selected comparisons
recovers the abutment target map. -/
@[reassoc, stacks 015N "target-map computation for the Grothendieck abutment comparison"]
theorem abutment_target_map
    {G : B ⥤ C} [G.Additive] {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}
    {X Y : DerivedCategory.Plus A} {f : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (m : Map f S T) (n : ℤ) :
    (S.abutmentIso n).inv ≫
        HomologicalComplex.homologyMap (S.filtered.underlyingMap m.filteredMap) n ≫
        (T.abutmentIso n).hom =
      abutmentMap RGF f n := sorry

end Map

end SpectralSequence

end CategoryTheory.Functor.RightDerived.Grothendieck
