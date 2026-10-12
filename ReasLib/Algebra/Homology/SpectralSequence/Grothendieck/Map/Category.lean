/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Map

/-!
# Identity and Composition of Grothendieck Spectral-Sequence Maps

The non-Prop data of identity and composition are fixed explicitly.  The induced-map and
naturality obligations remain separate theorem statements, which keeps the computational map
owners free of hidden choices.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB wC v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence.Map

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Abelian A] [Abelian B] [Abelian C]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable [HasDerivedCategory.{wC} C] [HasInjectiveResolutions B]
variable {G : B ⥤ C} [G.Additive]
variable {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
variable {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}

/-- The identity maps commute with every chosen second-page comparison. -/
theorem idPageTwo {X : DerivedCategory.Plus A}
    (S : SpectralSequence G RF RGF X) :
    ∀ (p : ℕ) (q : ℤ),
      CommSq (((𝟙 S.sequence : S.sequence ⟶ S.sequence).hom 2).f (Int.ofNat p, q))
        (S.pageTwoIso p q).hom (S.pageTwoIso p q).hom
        (pageTwoMap G RF (𝟙 X) p q) := sorry

/-- The identity morphism of a Grothendieck spectral-sequence realization. -/
@[stacks 015N "identity map of a Grothendieck spectral sequence"]
noncomputable def id {X : DerivedCategory.Plus A}
    (S : SpectralSequence G RF RGF X) :
    SpectralSequence.Map (𝟙 X) S S where
  toWithAbutmentMap :=
    FilteredComplex.SpectralSequence.Realization.WithAbutment.Map.id
      (abutmentFunctor RGF) S.toWithAbutment
  pageTwoSq := idPageTwo S

/-- The functorial-abutment map underlying the identity is the neutral identity map. -/
@[simp, stacks 015N "identity map of a Grothendieck spectral sequence"]
theorem id_toWithAbutmentMap {X : DerivedCategory.Plus A}
    (S : SpectralSequence G RF RGF X) :
    (Map.id S).toWithAbutmentMap =
      FilteredComplex.SpectralSequence.Realization.WithAbutment.Map.id
        (abutmentFunctor RGF) S.toWithAbutment := sorry

/-- The underlying realization map of the identity is the canonical identity realization map. -/
@[simp, stacks 015N "identity map of a Grothendieck spectral sequence"]
theorem id_toMap {X : DerivedCategory.Plus A}
    (S : SpectralSequence G RF RGF X) :
    (Map.id S).toMap =
      FilteredComplex.SpectralSequence.Realization.Map.id S.toRealization := sorry

/-- The filtered-complex component of the identity spectral-sequence map. -/
@[simp, stacks 015N "identity map of a Grothendieck spectral sequence"]
theorem id_filteredMap {X : DerivedCategory.Plus A}
    (S : SpectralSequence G RF RGF X) :
    (Map.id S).filteredMap = 𝟙 S.filtered := sorry

/-- The spectral-sequence component of the identity spectral-sequence map. -/
@[simp, stacks 015N "identity map of a Grothendieck spectral sequence"]
theorem id_sequenceMap {X : DerivedCategory.Plus A}
    (S : SpectralSequence G RF RGF X) :
    (Map.id S).sequenceMap = 𝟙 S.sequence := sorry

/-- The association morphism of the identity Grothendieck map is the neutral identity. -/
@[simp, stacks 015N "identity association morphism of a Grothendieck spectral sequence"]
theorem toAssociationHom_id {X : DerivedCategory.Plus A}
    (S : SpectralSequence G RF RGF X) :
    (Map.id S).toAssociationHom =
      FilteredComplex.Association.Hom.id S.association := sorry

/-- Composite maps commute with every chosen second-page comparison. -/
theorem compPageTwo {X Y Z : DerivedCategory.Plus A} {f : X ⟶ Y} {g : Y ⟶ Z}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    {U : SpectralSequence G RF RGF Z}
    (m : SpectralSequence.Map f S T) (n : SpectralSequence.Map g T U) :
    ∀ (p : ℕ) (q : ℤ),
      CommSq (((m.sequenceMap ≫ n.sequenceMap).hom 2).f (Int.ofNat p, q))
        (S.pageTwoIso p q).hom (U.pageTwoIso p q).hom
        (pageTwoMap G RF (f ≫ g) p q) := sorry

/-- The composite of maps of Grothendieck spectral-sequence realizations. -/
@[stacks 015N "composition of maps of Grothendieck spectral sequences"]
noncomputable def comp
    {X Y Z : DerivedCategory.Plus A} {f : X ⟶ Y} {g : Y ⟶ Z}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    {U : SpectralSequence G RF RGF Z}
    (m : SpectralSequence.Map f S T) (n : SpectralSequence.Map g T U) :
    SpectralSequence.Map (f ≫ g) S U where
  toWithAbutmentMap :=
    FilteredComplex.SpectralSequence.Realization.WithAbutment.Map.comp
      (abutmentFunctor RGF) m.toWithAbutmentMap n.toWithAbutmentMap
  pageTwoSq := compPageTwo m n

/-- The functorial-abutment map underlying a composite is the neutral composite map. -/
@[simp, stacks 015N "composition of maps of Grothendieck spectral sequences"]
theorem comp_toWithAbutmentMap
    {X Y Z : DerivedCategory.Plus A} {f : X ⟶ Y} {g : Y ⟶ Z}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    {U : SpectralSequence G RF RGF Z}
    (m : Map f S T) (n : Map g T U) :
    (Map.comp m n).toWithAbutmentMap =
      FilteredComplex.SpectralSequence.Realization.WithAbutment.Map.comp
        (abutmentFunctor RGF) m.toWithAbutmentMap n.toWithAbutmentMap := sorry

/-- The underlying realization map of a composite is the composite realization map. -/
@[simp, stacks 015N "composition of maps of Grothendieck spectral sequences"]
theorem comp_toMap
    {X Y Z : DerivedCategory.Plus A} {f : X ⟶ Y} {g : Y ⟶ Z}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    {U : SpectralSequence G RF RGF Z}
    (m : Map f S T) (n : Map g T U) :
    (Map.comp m n).toMap =
      FilteredComplex.SpectralSequence.Realization.Map.comp m.toMap n.toMap := sorry

/-- The filtered-complex component of a composite spectral-sequence map. -/
@[simp, stacks 015N "composition of maps of Grothendieck spectral sequences"]
theorem comp_filteredMap {X Y Z : DerivedCategory.Plus A} {f : X ⟶ Y} {g : Y ⟶ Z}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    {U : SpectralSequence G RF RGF Z}
    (m : Map f S T) (n : Map g T U) :
    (Map.comp m n).filteredMap = m.filteredMap ≫ n.filteredMap := sorry

/-- The spectral-sequence component of a composite spectral-sequence map. -/
@[simp, stacks 015N "composition of maps of Grothendieck spectral sequences"]
theorem comp_sequenceMap {X Y Z : DerivedCategory.Plus A} {f : X ⟶ Y} {g : Y ⟶ Z}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    {U : SpectralSequence G RF RGF Z}
    (m : Map f S T) (n : Map g T U) :
    (Map.comp m n).sequenceMap = m.sequenceMap ≫ n.sequenceMap := sorry

/-- The association morphism of a composite Grothendieck map is the composite association
morphism. -/
@[simp, stacks 015N "composite association morphism of a Grothendieck spectral sequence"]
theorem toAssociationHom_comp
    {X Y Z : DerivedCategory.Plus A} {f : X ⟶ Y} {g : Y ⟶ Z}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    {U : SpectralSequence G RF RGF Z}
    (m : Map f S T) (n : Map g T U) :
    (Map.comp m n).toAssociationHom =
      FilteredComplex.Association.Hom.comp m.toAssociationHom n.toAssociationHom := sorry

/-- Reindex a Grothendieck spectral-sequence map along an equality of its underlying
derived-category morphisms. -/
@[stacks 015N "reindexing maps of Grothendieck spectral sequences"]
def reindex
    {X Y : DerivedCategory.Plus A} {f g : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (h : f = g) (m : Map f S T) : Map g S T :=
  h ▸ m

/-- Reindexing is inherited from the neutral functorial-abutment map. -/
@[simp, stacks 015N "reindexing maps of Grothendieck spectral sequences"]
theorem reindex_toWithAbutmentMap
    {X Y : DerivedCategory.Plus A} {f g : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (h : f = g) (m : Map f S T) :
    (Map.reindex h m).toWithAbutmentMap =
      FilteredComplex.SpectralSequence.Realization.WithAbutment.Map.reindex
        (abutmentFunctor RGF) h m.toWithAbutmentMap := sorry

/-- Reindexing leaves the underlying realization map unchanged. -/
@[simp, stacks 015N "reindexing maps of Grothendieck spectral sequences"]
theorem reindex_toMap
    {X Y : DerivedCategory.Plus A} {f g : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (h : f = g) (m : Map f S T) :
    (Map.reindex h m).toMap = m.toMap := sorry

/-- Reindexing leaves the filtered-complex component unchanged. -/
@[simp, stacks 015N "reindexing maps of Grothendieck spectral sequences"]
theorem reindex_filteredMap
    {X Y : DerivedCategory.Plus A} {f g : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (h : f = g) (m : Map f S T) :
    (Map.reindex h m).filteredMap = m.filteredMap := sorry

/-- Reindexing leaves the spectral-sequence component unchanged. -/
@[simp, stacks 015N "reindexing maps of Grothendieck spectral sequences"]
theorem reindex_sequenceMap
    {X Y : DerivedCategory.Plus A} {f g : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (h : f = g) (m : Map f S T) :
    (Map.reindex h m).sequenceMap = m.sequenceMap := sorry

/-- Reindexing leaves the association morphism unchanged after transporting its filtered-map
index. -/
@[simp, stacks 015N "reindexing association morphisms of Grothendieck spectral sequences"]
theorem toAssociationHom_reindex
    {X Y : DerivedCategory.Plus A} {f g : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (h : f = g) (m : Map f S T) :
    ((reindex_filteredMap h m) ▸ (Map.reindex h m).toAssociationHom) =
      m.toAssociationHom := sorry

/-- Reindexing along reflexivity leaves a Grothendieck spectral-sequence map unchanged. -/
@[simp, stacks 015N "reindexing maps of Grothendieck spectral sequences"]
theorem reindex_rfl
    {X Y : DerivedCategory.Plus A} {f : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (m : Map f S T) :
    Map.reindex rfl m = m := sorry

/-- Successive reindexings of a Grothendieck spectral-sequence map combine by transitivity. -/
@[simp, stacks 015N "transitivity of Grothendieck spectral-sequence map transport"]
theorem reindex_trans
    {X Y : DerivedCategory.Plus A} {f f' f'' : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (e : f = f') (e' : f' = f'') (m : Map f S T) :
    Map.reindex e' (Map.reindex e m) = Map.reindex (e.trans e') m := sorry

/-- Reindexing along an equality and then its inverse recovers a Grothendieck map. -/
@[simp, stacks 015N "inverse Grothendieck spectral-sequence map transport"]
theorem reindex_symm
    {X Y : DerivedCategory.Plus A} {f f' : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (e : f = f') (m : Map f S T) :
    Map.reindex e.symm (Map.reindex e m) = m := sorry

/-- Reindexing the left factor of a composite Grothendieck map commutes with composition. -/
@[simp, stacks 015N "left-factor Grothendieck spectral-sequence map transport"]
theorem reindex_comp_left
    {X Y Z : DerivedCategory.Plus A} {f f' : X ⟶ Y} {g : Y ⟶ Z}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    {U : SpectralSequence G RF RGF Z} (e : f = f')
    (m : Map f S T) (n : Map g T U) :
    Map.reindex (congrArg (fun k : X ⟶ Y => k ≫ g) e) (Map.comp m n) =
      Map.comp (Map.reindex e m) n := sorry

/-- Reindexing the right factor of a composite Grothendieck map commutes with composition. -/
@[simp, stacks 015N "right-factor Grothendieck spectral-sequence map transport"]
theorem reindex_comp_right
    {X Y Z : DerivedCategory.Plus A} {f : X ⟶ Y} {g g' : Y ⟶ Z}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    {U : SpectralSequence G RF RGF Z} (e : g = g')
    (m : Map f S T) (n : Map g T U) :
    Map.reindex (congrArg (fun k : Y ⟶ Z => f ≫ k) e) (Map.comp m n) =
      Map.comp m (Map.reindex e n) := sorry

/-- Reindexing both factors of a composite Grothendieck map commutes with composition. -/
@[simp, stacks 015N "two-factor Grothendieck spectral-sequence map transport"]
theorem reindex_comp
    {X Y Z : DerivedCategory.Plus A} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    {U : SpectralSequence G RF RGF Z} (e : f = f') (e' : g = g')
    (m : Map f S T) (n : Map g T U) :
    Map.reindex (congrArg₂ (fun (a : X ⟶ Y) (b : Y ⟶ Z) => a ≫ b) e e')
        (Map.comp m n) =
      Map.comp (Map.reindex e m) (Map.reindex e' n) := sorry

/-- The identity map is a left identity after reindexing the underlying morphism. -/
@[stacks 015N "left identity for maps of Grothendieck spectral sequences"]
theorem id_comp
    {X Y : DerivedCategory.Plus A} {f : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (m : Map f S T) :
    Map.reindex (Category.id_comp f) (Map.comp (Map.id S) m) = m := sorry

/-- The identity map is a right identity after reindexing the underlying morphism. -/
@[stacks 015N "right identity for maps of Grothendieck spectral sequences"]
theorem comp_id
    {X Y : DerivedCategory.Plus A} {f : X ⟶ Y}
    {S : SpectralSequence G RF RGF X} {T : SpectralSequence G RF RGF Y}
    (m : Map f S T) :
    Map.reindex (Category.comp_id f) (Map.comp m (Map.id T)) = m := sorry

/-- Composition of Grothendieck spectral-sequence maps is associative after reindexing the
underlying morphism. -/
@[stacks 015N "associativity for maps of Grothendieck spectral sequences"]
theorem assoc
    {W X Y Z : DerivedCategory.Plus A}
    {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z}
    {R : SpectralSequence G RF RGF W} {S : SpectralSequence G RF RGF X}
    {T : SpectralSequence G RF RGF Y} {U : SpectralSequence G RF RGF Z}
    (m : Map f R S) (n : Map g S T) (k : Map h T U) :
    Map.reindex (Category.assoc f g h) (Map.comp (Map.comp m n) k) =
      Map.comp m (Map.comp n k) := sorry

end CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence.Map
