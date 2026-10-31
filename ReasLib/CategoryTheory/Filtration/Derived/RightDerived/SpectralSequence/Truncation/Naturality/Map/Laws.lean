/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Map.Identity
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Map.Composition
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Map.Reindex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Laws for truncation-filtration realization maps

Bundling the representative lift in a realization map makes its transport and category laws agree
with the generic and stupid-filtration realization-map APIs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

namespace Realization

-- Keep all three concrete morphisms: equality does not require any uniqueness theorem
-- for spectral-sequence maps or any of the upstream category-law placeholders.
private theorem Map.ext_data
    {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} {m n : Map F f S T}
    (hlift : m.lift.hom = n.lift.hom)
    (hresolution : m.original.resolutionMap.hom = n.original.resolutionMap.hom)
    (hsequence : m.original.sequenceMap = n.original.sequenceMap) : m = n := by
  rcases m with ⟨⟨lh, lc⟩, ⟨⟨rh, rc⟩, compatible, ⟨sh, sc⟩⟩, pageTwo, target⟩
  rcases n with ⟨⟨lh', lc'⟩, ⟨⟨rh', rc'⟩, compatible', ⟨sh', sc'⟩⟩, pageTwo', target'⟩
  change lh = lh' at hlift
  cases hlift
  change rh = rh' at hresolution
  cases hresolution
  change sh = sh' at hsequence
  cases hsequence
  rfl

/-- Transport the original generic realization map along an equality of the chosen lifts.
This packages the dependent change from `m.lift.hom` to `n.lift.hom` as an ordinary map. -/
@[stacks 0BKM "transported original map of a truncation realization"]
noncomputable def Map.originalCast
    {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} {m n : Map F f S T}
    (h : m.lift = n.lift) :
    RightDerived.SpectralSequence.Realization.Map F
      (CochainComplex.TruncationFiltration.map n.lift.hom) S.original T.original :=
  RightDerived.SpectralSequence.Realization.Map.reindex F
    (congrArg (fun l : DerivedCategory.Preimage.Lift f =>
      CochainComplex.TruncationFiltration.map l.hom) h) m.original

/-- Transporting an original component along reflexivity changes no data. -/
@[simp, stacks 0BKM "reflexive transport of a truncation original map"]
theorem Map.originalCast_rfl
    {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    Map.originalCast F (m := m) (n := m) rfl = m.original := by
  rfl

/-- Reindexing the left factor of a composite commutes with composition. -/
@[simp, stacks 0BKM "left-factor transport of truncation realization maps"]
theorem Map.reindex_comp_left
    {K L M : DerivedCategory A} {f f' : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (e : f = f') (m : Map F f S T) (n : Map F g T U) :
    Map.reindex F (congrArg (fun k : K ⟶ L => k ≫ g) e) (Map.comp F m n) =
      Map.comp F (Map.reindex F e m) n := by
  cases e
  rfl

/-- Reindexing the right factor of a composite commutes with composition. -/
@[simp, stacks 0BKM "right-factor transport of truncation realization maps"]
theorem Map.reindex_comp_right
    {K L M : DerivedCategory A} {f : K ⟶ L} {g g' : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (e : g = g') (m : Map F f S T) (n : Map F g T U) :
    Map.reindex F (congrArg (fun k : L ⟶ M => f ≫ k) e) (Map.comp F m n) =
      Map.comp F m (Map.reindex F e n) := by
  cases e
  rfl

/-- Reindexing both factors of a composite commutes with composition. -/
@[simp, stacks 0BKM "two-factor transport of truncation realization maps"]
theorem Map.reindex_comp
    {K L M : DerivedCategory A} {f f' : K ⟶ L} {g g' : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (e : f = f') (e' : g = g') (m : Map F f S T) (n : Map F g T U) :
    Map.reindex F (congrArg₂ (fun (a : K ⟶ L) (b : L ⟶ M) => a ≫ b) e e')
        (Map.comp F m n) =
      Map.comp F (Map.reindex F e m) (Map.reindex F e' n) := by
  cases e
  cases e'
  rfl

/-- Identity is a left unit for truncation-filtration realization maps after base transport. -/
@[stacks 0BKM "left identity law for truncation realization maps"]
theorem Map.id_comp
    {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    Map.reindex F (Category.id_comp f) (Map.comp F (Map.id F S) m) = m := by
  apply Map.ext_data
  · change 𝟙 _ ≫ m.lift.hom = m.lift.hom
    exact Category.id_comp _
  · change 𝟙 _ ≫ m.original.resolutionMap.hom = m.original.resolutionMap.hom
    exact Category.id_comp _
  · change 𝟙 _ ≫ m.original.sequenceMap = m.original.sequenceMap
    exact Category.id_comp _

/-- Identity is a right unit for truncation-filtration realization maps after base transport. -/
@[stacks 0BKM "right identity law for truncation realization maps"]
theorem Map.comp_id
    {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    Map.reindex F (Category.comp_id f) (Map.comp F m (Map.id F T)) = m := by
  apply Map.ext_data
  · change m.lift.hom ≫ 𝟙 _ = m.lift.hom
    exact Category.comp_id _
  · change m.original.resolutionMap.hom ≫ 𝟙 _ = m.original.resolutionMap.hom
    exact Category.comp_id _
  · change m.original.sequenceMap ≫ 𝟙 _ = m.original.sequenceMap
    exact Category.comp_id _

/-- Composition of truncation-filtration realization maps is associative after base transport. -/
@[stacks 0BKM "associativity law for truncation realization maps"]
theorem Map.assoc
    {K L M N : DerivedCategory A} {f : K ⟶ L} {g : L ⟶ M} {h : M ⟶ N}
    {S : Realization F K} {T : Realization F L}
    {U : Realization F M} {V : Realization F N}
    (a : Map F f S T) (b : Map F g T U) (c : Map F h U V) :
    Map.reindex F (Category.assoc f g h) (Map.comp F (Map.comp F a b) c) =
      Map.comp F a (Map.comp F b c) := by
  apply Map.ext_data
  · change (a.lift.hom ≫ b.lift.hom) ≫ c.lift.hom =
      a.lift.hom ≫ b.lift.hom ≫ c.lift.hom
    exact Category.assoc _ _ _
  · change (a.original.resolutionMap.hom ≫ b.original.resolutionMap.hom) ≫
        c.original.resolutionMap.hom =
      a.original.resolutionMap.hom ≫ b.original.resolutionMap.hom ≫
        c.original.resolutionMap.hom
    exact Category.assoc _ _ _
  · change (a.original.sequenceMap ≫ b.original.sequenceMap) ≫ c.original.sequenceMap =
      a.original.sequenceMap ≫ b.original.sequenceMap ≫ c.original.sequenceMap
    exact Category.assoc _ _ _

/-- Two truncation-filtration realization maps are equal when their lifts and original generic
maps agree dependently. -/
@[ext, stacks 0BKM "extensionality of truncation realization maps"]
theorem Map.ext
    {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} {m n : Map F f S T}
    (hlift : m.lift = n.lift) (horiginal : HEq m.original n.original) : m = n := by
  cases m
  cases n
  cases hlift
  cases horiginal
  rfl

/-- Two truncation-filtration realization maps are equal when their lifts agree and the
transported original generic maps agree by ordinary equality. -/
@[stacks 0BKM "extensionality of truncation realization maps after lift transport"]
theorem Map.ext_of_lift
    {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} {m n : Map F f S T}
    (hlift : m.lift = n.lift)
    (horiginal : Map.originalCast F hlift = n.original) : m = n := by
  apply Map.ext F hlift
  cases m
  cases n
  cases hlift
  exact heq_of_eq horiginal

end Realization

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation
