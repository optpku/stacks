/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ClosedSubspace.Basic
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealQuotient.ClosedImmersion
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealQuotient.Factorization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison of associated closed subspaces

This leaf compares any realization of an associated closed subspace with the canonical ideal
quotient. The forward map is explicit quotient-eliminator data. Invertibility and uniqueness are
exposed as propositions; no inverse is extracted from a deferred `IsIso` proof.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y Z : LocallyRingedSpace.{u}}
variable {I : IdealSubobject Y} {f : X ⟶ Y} {i : Z ⟶ Y}

/-- The canonical map from an associated closed subspace to the ideal quotient representing its
specified ideal. -/
@[stacks 01HO "comparison with the canonical ideal quotient"]
noncomputable def ClosedSubspace.IsAssociated.toIdealQuotient
    (hi : ClosedSubspace.IsAssociated i I) :
    Z ⟶ IdealQuotient.space I :=
  IdealQuotient.lift I i hi.le_kernel

/-- The canonical comparison with the ideal quotient lies over the ambient locally ringed
space. -/
@[reassoc, simp, stacks 01HO "canonical ideal-quotient comparison triangle"]
theorem ClosedSubspace.IsAssociated.toIdealQuotient_ι
    (hi : ClosedSubspace.IsAssociated i I) :
    hi.toIdealQuotient ≫ IdealQuotient.ι I = i :=
  IdealQuotient.lift_comp_ι I i hi.le_kernel

/-- The canonical comparison is the unique morphism from an associated realization to the ideal
quotient over the ambient locally ringed space. -/
@[stacks 01HO "canonical ideal-quotient comparison uniqueness"]
theorem ClosedSubspace.IsAssociated.toIdealQuotient_unique
    (hi : ClosedSubspace.IsAssociated i I)
    (g : Z ⟶ IdealQuotient.space I) (hg : g ≫ IdealQuotient.ι I = i) :
    g = hi.toIdealQuotient :=
  IdealQuotient.lift_unique I i hi.le_kernel g hg

/-- Two realizations of the same associated closed subspace have a unique comparison morphism
over the ambient space. -/
@[stacks 01HO "unique comparison of associated closed subspaces"]
theorem ClosedSubspace.IsAssociated.existsUnique_hom
    (hf : ClosedSubspace.IsAssociated f I)
    (hi : ClosedSubspace.IsAssociated i I) :
    ∃! g : X ⟶ Z, g ≫ i = f := sorry

/-- Comparison morphisms over the ambient space into an associated closed subspace are equal. -/
@[stacks 01HO "extensionality for associated closed subspaces"]
theorem ClosedSubspace.IsAssociated.hom_ext
    (hi : ClosedSubspace.IsAssociated i I)
    {g g' : X ⟶ Z} (hg : g ≫ i = f) (hg' : g' ≫ i = f) :
    g = g' := by
  have hclosed := hi.toIsClosedImmersion.isClosedEmbedding
  haveI : Mono i.toShHom :=
    SheafedSpace.mono_of_base_injective_of_stalk_epi i.toShHom hclosed.injective
      fun z => by
        have hpush : IsIso (Z.presheaf.stalkPushforward CommRingCat i.base z) :=
          TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing CommRingCat
            hclosed.isInducing Z.presheaf z
        have hsurj :=
          (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks i.toHom.c).mp
            hi.toIsClosedImmersion.toIsLocallySurjective
            (i.base z)
        change Epi ((TopCat.Presheaf.stalkFunctor CommRingCat (i.base z)).map i.toHom.c ≫
          Z.presheaf.stalkPushforward CommRingCat i.base z)
        exact epi_comp' (ConcreteCategory.epi_of_surjective _ hsurj)
          (@IsIso.epi_of_iso _ _ _ _ _ hpush)
  haveI : Mono i := forgetToSheafedSpace.mono_of_mono_map
    (inferInstance : Mono i.toShHom)
  exact (cancel_mono i).mp (hg.trans hg'.symm)

/-- Morphisms in the slice category into an associated closed subspace form a subsingleton. -/
@[stacks 01HO "slice morphisms into an associated closed subspace"]
theorem ClosedSubspace.IsAssociated.overHom_subsingleton
    (hi : ClosedSubspace.IsAssociated i I) (f : X ⟶ Y) :
    Subsingleton (Over.mk f ⟶ Over.mk i) := by
  refine ⟨fun g g' => ?_⟩
  apply Over.OverMorphism.ext
  exact hi.hom_ext (Over.w g) (Over.w g')

/-- Lemma 26.4.5: two realizations of the same associated closed subspace are uniquely
isomorphic over the ambient space. -/
@[stacks 01HO]
theorem ClosedSubspace.IsAssociated.existsUnique_iso
    (hf : ClosedSubspace.IsAssociated f I)
    (hi : ClosedSubspace.IsAssociated i I) :
    ∃! e : X ≅ Z, e.hom ≫ i = f := by
  obtain ⟨g, hg, huniq⟩ := hf.existsUnique_hom hi
  obtain ⟨h, hh, _⟩ := hi.existsUnique_hom hf
  have hgh : g ≫ h = 𝟙 X :=
    hf.hom_ext (by rw [Category.assoc, hh, hg]) (Category.id_comp f)
  have hhg : h ≫ g = 𝟙 Z :=
    hi.hom_ext (by rw [Category.assoc, hg, hh]) (Category.id_comp i)
  refine ⟨⟨g, h, hgh, hhg⟩, hg, ?_⟩
  intro e he
  exact Iso.ext (huniq e.hom he)

/-- The canonical comparison from an associated realization to the ideal quotient is
invertible. -/
@[stacks 01HO "associated realization comparison is invertible"]
theorem ClosedSubspace.IsAssociated.toIdealQuotient_isIso
    (hi : ClosedSubspace.IsAssociated i I) :
    IsIso hi.toIdealQuotient := by
  letI : I.IsLocallyGeneratedBySections := by
    rw [← hi.ideal_eq]
    exact hi.toIsClosedImmersion.idealSheafLocallyGenerated
  obtain ⟨e, he, _⟩ := hi.existsUnique_iso (IdealQuotient.ι_isAssociated I)
  have heq : e.hom = hi.toIdealQuotient := hi.toIdealQuotient_unique e.hom he
  exact heq ▸ e.isIso_hom

/-- A closed immersion is uniquely isomorphic over its target to any realization of the closed
subspace attached to its kernel ideal. -/
@[stacks 01HO "kernel ideal"]
theorem IsClosedImmersion.existsUnique_iso_to_associated
    (hf : IsClosedImmersion f)
    (hi : ClosedSubspace.IsAssociated i (Hom.kernelIdealSubobject f)) :
    ∃! e : X ≅ Z, e.hom ≫ i = f :=
  ClosedSubspace.IsAssociated.existsUnique_iso ⟨hf, rfl⟩ hi

/-- Isomorphisms in the slice category into an associated closed subspace form a subsingleton. -/
@[stacks 01HO "slice isomorphisms into an associated closed subspace"]
theorem ClosedSubspace.IsAssociated.overIso_subsingleton
    (hi : ClosedSubspace.IsAssociated i I) (f : X ⟶ Y) :
    Subsingleton (Over.mk f ≅ Over.mk i) := by
  letI := hi.overHom_subsingleton f
  exact ⟨fun e e' => Iso.ext (Subsingleton.elim e.hom e'.hom)⟩

end AlgebraicGeometry.LocallyRingedSpace
