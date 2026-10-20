/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Model.Comparison.Resolution
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Realization.Map.Definition

/-!
# Finite Right-Derived Realizations from Strict Resolutions

A strict filtered-injective resolution canonically determines the comparison with the pointwise
right-derived values, but it does not determine a spectral sequence associated to its filtered
model.  This leaf therefore retains the associated spectral sequence as explicit data while
installing `Model.Comparison.ofResolution` as the comparison field.

For maps between such realizations, compatibility of the canonical comparisons is automatic.
Only the resolution map and the genuinely data-bearing association morphism remain as inputs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open CochainComplex.FilteredInjectivePlus

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

namespace Realization

/-- Build a finite right-derived realization from a strict filtered-injective resolution and an
explicit spectral sequence associated to its filtered model.  The model comparison is the
canonical `Model.Comparison.ofResolution`. -/
@[stacks 015W "finite right-derived realization from a strict filtered-injective resolution"]
noncomputable def ofResolution (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K)
    (E : FilteredComplex.AssociatedSpectralSequence (model T R)) :
    Realization T K where
  resolution := R
  comparison := Model.Comparison.ofResolution T R
  associated := E

/-- The resolution retained by `ofResolution` is its input resolution. -/
@[simp, stacks 015W "resolution of the canonical finite right-derived realization"]
theorem ofResolution_resolution (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K)
    (E : FilteredComplex.AssociatedSpectralSequence (model T R)) :
    (ofResolution T R E).resolution = R := sorry

/-- The comparison retained by `ofResolution` is the canonical resolution comparison. -/
@[simp, stacks 015W "comparison of the canonical finite right-derived realization"]
theorem ofResolution_comparison (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K)
    (E : FilteredComplex.AssociatedSpectralSequence (model T R)) :
    (ofResolution T R E).comparison = Model.Comparison.ofResolution T R := sorry

/-- The associated spectral sequence retained by `ofResolution` is its explicit input. -/
@[simp, stacks 015W "association data of the canonical finite right-derived realization"]
theorem ofResolution_associated (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K)
    (E : FilteredComplex.AssociatedSpectralSequence (model T R)) :
    (ofResolution T R E).associated = E := sorry

/-- The filtered model underlying `ofResolution` is the model of its input resolution. -/
@[simp, stacks 015W "filtered model of the canonical finite right-derived realization"]
theorem ofResolution_filtered (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K)
    (E : FilteredComplex.AssociatedSpectralSequence (model T R)) :
    (ofResolution T R E).filtered = model T R := sorry

/-- The spectral sequence underlying `ofResolution` is the selected associated sequence. -/
@[simp, stacks 015W "spectral sequence of the canonical finite right-derived realization"]
theorem ofResolution_sequence (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K)
    (E : FilteredComplex.AssociatedSpectralSequence (model T R)) :
    (ofResolution T R E).sequence = E.sequence := sorry

/-- The association underlying `ofResolution` is the selected concrete association. -/
@[simp, stacks 015W "association of the canonical finite right-derived realization"]
theorem ofResolution_association (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K)
    (E : FilteredComplex.AssociatedSpectralSequence (model T R)) :
    (ofResolution T R E).association = E.association := sorry

/-- The first-page comparison of `ofResolution` uses the selected association followed by the
canonical graded-piece resolution comparison. -/
@[simp, stacks 015W "first page of the canonical finite right-derived realization"]
theorem ofResolution_pageOneIso (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K)
    (E : FilteredComplex.AssociatedSpectralSequence (model T R)) (p q : ℤ) :
    (ofResolution T R E).pageOneIso p q =
      E.association.pageOneIso p q ≪≫
        (Model.Comparison.ofResolution T R).gradedPieceIso p (p + q) := sorry

/-- The abutment comparison of `ofResolution` is the canonical underlying resolution
comparison. -/
@[simp, stacks 015W "abutment of the canonical finite right-derived realization"]
theorem ofResolution_targetIso (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K)
    (E : FilteredComplex.AssociatedSpectralSequence (model T R)) (n : ℤ) :
    (ofResolution T R E).targetIso n =
      (Model.Comparison.ofResolution T R).underlyingIso n := sorry

/-- A strict filtered-injective resolution determines a finite right-derived realization up to
the noncanonical choice of an associated spectral sequence. -/
@[stacks 015W "existence of a finite right-derived realization from a strict resolution"]
theorem nonemptyOfResolution (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K) :
    Nonempty (Realization T K) := sorry

namespace Map

/-- Build a map between canonical-resolution realizations from a resolution map and an
association morphism.  Compatibility of the model comparisons is supplied automatically by
`Model.Comparison.IsCompatible.ofResolution`. -/
@[stacks 015W "map between canonical finite right-derived realizations"]
noncomputable def ofResolution {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L}
    {P : FilteredComplex.AssociatedSpectralSequence (model T R)}
    {Q : FilteredComplex.AssociatedSpectralSequence (model T S)}
    (m : Resolution.Map f R S)
    (a : FilteredComplex.Association.Hom P.association Q.association (modelMap T m)) :
    Map f (Realization.ofResolution T R P) (Realization.ofResolution T S Q) :=
  ofResolutionMap m (Model.Comparison.IsCompatible.ofResolution T m) a

/-- The resolution-map component of `Map.ofResolution` is its input resolution map. -/
@[simp, stacks 015W "resolution component of a canonical finite realization map"]
theorem ofResolution_resolutionMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L}
    {P : FilteredComplex.AssociatedSpectralSequence (model T R)}
    {Q : FilteredComplex.AssociatedSpectralSequence (model T S)}
    (m : Resolution.Map f R S)
    (a : FilteredComplex.Association.Hom P.association Q.association (modelMap T m)) :
    (ofResolution m a).resolutionMap = m := sorry

/-- The association-map component of `Map.ofResolution` is its input association morphism. -/
@[simp, stacks 015W "association component of a canonical finite realization map"]
theorem ofResolution_associationMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L}
    {P : FilteredComplex.AssociatedSpectralSequence (model T R)}
    {Q : FilteredComplex.AssociatedSpectralSequence (model T S)}
    (m : Resolution.Map f R S)
    (a : FilteredComplex.Association.Hom P.association Q.association (modelMap T m)) :
    (ofResolution m a).associationMap = a := sorry

/-- The filtered-model component of `Map.ofResolution` is induced by its resolution map. -/
@[simp, stacks 015W "filtered component of a canonical finite realization map"]
theorem ofResolution_filteredMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L}
    {P : FilteredComplex.AssociatedSpectralSequence (model T R)}
    {Q : FilteredComplex.AssociatedSpectralSequence (model T S)}
    (m : Resolution.Map f R S)
    (a : FilteredComplex.Association.Hom P.association Q.association (modelMap T m)) :
    (ofResolution m a).filteredMap = modelMap T m := sorry

/-- The spectral-sequence component of `Map.ofResolution` is the morphism stored by its
association input. -/
@[simp, stacks 015W "spectral-sequence component of a canonical finite realization map"]
theorem ofResolution_sequenceMap {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L}
    {P : FilteredComplex.AssociatedSpectralSequence (model T R)}
    {Q : FilteredComplex.AssociatedSpectralSequence (model T S)}
    (m : Resolution.Map f R S)
    (a : FilteredComplex.Association.Hom P.association Q.association (modelMap T m)) :
    (ofResolution m a).sequenceMap = a.hom := sorry

/-- A resolution map between canonical-resolution realizations lifts to a realization map.  This
is an existence statement: no association morphism is selected as public data. -/
@[stacks 015W "existence of a map between canonical finite right-derived realizations"]
theorem nonemptyOfResolution {T : A ⥤ₗ B} [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L}
    (P : FilteredComplex.AssociatedSpectralSequence (model T R))
    (Q : FilteredComplex.AssociatedSpectralSequence (model T S))
    (m : Resolution.Map f R S) :
    Nonempty (Map f (Realization.ofResolution T R P) (Realization.ofResolution T S Q)) := sorry

end Map

end Realization

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
