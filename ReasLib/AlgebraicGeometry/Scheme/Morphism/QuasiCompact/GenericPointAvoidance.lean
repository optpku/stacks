module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Valuation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Avoiding a missing generic point

A quasi-compact scheme morphism whose image misses the generic point of an irreducible component
misses an open neighbourhood of that point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- If the image of a quasi-compact scheme morphism misses the generic point of an irreducible
component of the target, it misses an open neighbourhood of that point. -/
@[stacks 02NE]
theorem exists_open_preimage_eq_bot_of_genericPoint_not_mem_range
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    {η : S} {Z : irreducibleComponents S} (hηZ : IsGenericPoint η (Z : Set S))
    (hη : η ∉ Set.range f.base) :
    ∃ V : S.Opens, η ∈ V ∧ f ⁻¹ᵁ V = ⊥ := by
  have hηimage : η ∉ Set.range (Scheme.Hom.imageι f).base := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hxz⟩ :=
      exists_specialization_from_image_of_mem_schemeTheoreticImage f z
    have hxη := hxz.map (Scheme.Hom.imageι f).continuous
    rw [hz] at hxη
    change ((Scheme.Hom.toImage f ≫ Scheme.Hom.imageι f) x) ⤳ η at hxη
    rw [Scheme.Hom.toImage_imageι] at hxη
    have hZsub : (Z : Set S) ⊆ closure ({f x} : Set S) :=
      (hηZ.mem_closed_set_iff isClosed_closure).mp
        (specializes_iff_mem_closure.mp hxη)
    have hclosure : closure ({f x} : Set S) = (Z : Set S) :=
      le_antisymm (Z.2.2 isIrreducible_singleton.closure hZsub) hZsub
    have hfxZ : IsGenericPoint (f x) (Z : Set S) := by
      rw [isGenericPoint_def, hclosure]
    exact hη ⟨x, (hηZ.eq hfxZ).symm⟩
  let V : S.Opens := ⟨(Set.range (Scheme.Hom.imageι f).base)ᶜ,
    isOpen_compl_iff.mpr (Scheme.Hom.imageι f).isClosedEmbedding.isClosed_range⟩
  refine ⟨V, hηimage, ?_⟩
  apply Opens.ext
  ext x
  change (f x ∉ Set.range (Scheme.Hom.imageι f).base) ↔ False
  simp only [iff_false, not_not]
  refine ⟨Scheme.Hom.toImage f x, ?_⟩
  change ((Scheme.Hom.toImage f ≫ Scheme.Hom.imageι f) x) = f x
  rw [Scheme.Hom.toImage_imageι]

end AlgebraicGeometry
