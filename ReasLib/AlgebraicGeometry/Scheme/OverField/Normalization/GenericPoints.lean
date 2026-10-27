/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Generic-point normalization prerequisites over a field

This leaf supplies the canonical finiteness and separation instances that let
the generic-point normalization construction operate on a scheme locally of
finite type over a field. The reduction and reduced irreducible-component
instances are kept here because they are the same prerequisites for the
normalization comparison maps, rather than chapter-specific consequences.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.Normalization

variable {k : Type u} [Field k]

namespace FiniteComponents

/-- A scheme locally of finite type over a field has finitely many irreducible
components on every quasi-compact open. -/
instance instOnCompactOpens
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X.left := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  infer_instance

end FiniteComponents

namespace GenericPoints

private theorem coproductTo_injective (X : Scheme.{u}) :
    Function.Injective (genericPointSpectrumCoproductTo X) := by
  let F : genericPoints X → Scheme.{u} := fun η ↦ Spec (X.residueField η.1)
  intro x y h
  obtain ⟨⟨η, s⟩, rfl⟩ := (sigmaMk F).surjective x
  obtain ⟨⟨ξ, t⟩, rfl⟩ := (sigmaMk F).surjective y
  have hη : η = ξ := Subtype.ext (by
    simp only [sigmaMk_mk] at h
    change (Limits.Sigma.ι F η ≫ genericPointSpectrumCoproductTo X) s =
      (Limits.Sigma.ι F ξ ≫ genericPointSpectrumCoproductTo X) t at h
    simpa only [F, genericPointSpectrumCoproductTo_ι,
      Scheme.fromSpecResidueField_apply] using h)
  subst ξ
  exact congrArg (fun z ↦ sigmaMk F ⟨η, z⟩) (Subsingleton.elim s t)

private theorem coproductTo_quasiSeparated (X : Scheme.{u}) :
    QuasiSeparated (genericPointSpectrumCoproductTo X) := by
  letI : IsSeparated (genericPointSpectrumCoproductTo X) :=
    isSeparated_of_injective _ (coproductTo_injective X)
  infer_instance

private theorem finite_genericPoints_inter (X : Scheme.{u})
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : Set X) (hU : IsOpen U) (hUc : IsCompact U) :
    (genericPoints X ∩ U).Finite := by
  let V : CompactOpens X := ⟨⟨U, hUc⟩, hU⟩
  haveI : Finite (genericPoints V) := genericPoints.finite
    (Scheme.HasFiniteIrreducibleComponentsOnCompactOpens.finite_irreducibleComponents V)
  have hf : Topology.IsOpenEmbedding (Subtype.val : V → X) := hU.isOpenEmbedding_subtypeVal
  let g : ↥(genericPoints X ∩ U) → genericPoints V := fun η ↦
    ⟨⟨η.1, η.2.2⟩, by
      have hsing : (Subtype.val : V → X) ⁻¹' {η.1} = {⟨η.1, η.2.2⟩} := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff]
      change closure ({⟨η.1, η.2.2⟩} : Set V) ∈ irreducibleComponents V
      rw [← hsing, ← hf.isOpenMap.preimage_closure_eq_closure_preimage hf.continuous]
      exact preimage_mem_irreducibleComponents η.2.1 hf
        ⟨η.1, subset_closure (Set.mem_singleton _), ⟨⟨η.1, η.2.2⟩, rfl⟩⟩⟩
  exact @Finite.of_injective _ _ inferInstance g fun η ξ h ↦
    Subtype.ext (congrArg (fun z : genericPoints V ↦ z.1.1) h)

private theorem coproductTo_quasiCompact (X : Scheme.{u})
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] :
    QuasiCompact (genericPointSpectrumCoproductTo X) := by
  constructor
  intro U hU hUc
  have hfinite := (finite_genericPoints_inter X U hU hUc).preimage (coproductTo_injective X).injOn
  have hpre : (genericPointSpectrumCoproductTo X) ⁻¹' U ⊆
      (genericPointSpectrumCoproductTo X) ⁻¹' (genericPoints X ∩ U) := by
    intro x hx
    refine ⟨?_, hx⟩
    let F : genericPoints X → Scheme.{u} := fun η ↦ Spec (X.residueField η.1)
    obtain ⟨⟨η, s⟩, rfl⟩ := (sigmaMk F).surjective x
    rw [sigmaMk_mk]
    change (Limits.Sigma.ι F η ≫ genericPointSpectrumCoproductTo X) s ∈ genericPoints X
    simpa only [F, genericPointSpectrumCoproductTo_ι, Scheme.fromSpecResidueField_apply] using η.2
  exact (hfinite.subset hpre).isCompact

/-- The generic-point residue-field coproduct of a scheme locally of finite
type over a field is quasi-compact. -/
instance instCoproductQuasiCompact
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    QuasiCompact (genericPointSpectrumCoproductTo X.left) :=
  coproductTo_quasiCompact X.left

/-- The generic-point residue-field coproduct of a scheme locally of finite
type over a field is quasi-separated. -/
instance instCoproductQuasiSeparated
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    QuasiSeparated (genericPointSpectrumCoproductTo X.left) :=
  coproductTo_quasiSeparated X.left

end GenericPoints

namespace Reduction

/-- The reduction of a scheme locally of finite type over a field remains
locally of finite type over that field. -/
instance instLocallyOfFiniteType
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType (X.left.nilradical.subschemeι ≫ X.hom) := by
  infer_instance

namespace GenericPoints

/-- The generic-point residue-field coproduct of the reduction of a scheme
locally of finite type over a field is quasi-compact. -/
instance instCoproductQuasiCompact
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    QuasiCompact (genericPointSpectrumCoproductTo X.left.nilradical.subscheme) :=
  @Normalization.GenericPoints.instCoproductQuasiCompact k _
    (Over.mk (X.left.nilradical.subschemeι ≫ X.hom))
    (Reduction.instLocallyOfFiniteType X)

/-- The generic-point residue-field coproduct of the reduction of a scheme
locally of finite type over a field is quasi-separated. -/
instance instCoproductQuasiSeparated
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    QuasiSeparated (genericPointSpectrumCoproductTo X.left.nilradical.subscheme) :=
  @Normalization.GenericPoints.instCoproductQuasiSeparated k _
    (Over.mk (X.left.nilradical.subschemeι ≫ X.hom))
    (Reduction.instLocallyOfFiniteType X)

end GenericPoints
end Reduction

namespace IrreducibleComponent

/-- A reduced irreducible-component subscheme of a scheme locally of finite
type over a field remains locally of finite type over that field. -/
instance instLocallyOfFiniteType
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (Z : irreducibleComponents X.left) :
    LocallyOfFiniteType (X.left.irreducibleComponentSubschemeι Z ≫ X.hom) := by
  infer_instance

namespace GenericPoints

/-- The generic-point residue-field coproduct of a reduced
irreducible-component subscheme over a field is quasi-compact. -/
instance instCoproductQuasiCompact
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (Z : irreducibleComponents X.left) :
    QuasiCompact (genericPointSpectrumCoproductTo
      (X.left.irreducibleComponentSubscheme Z)) :=
  @Normalization.GenericPoints.instCoproductQuasiCompact k _
    (Over.mk (X.left.irreducibleComponentSubschemeι Z ≫ X.hom))
    (IrreducibleComponent.instLocallyOfFiniteType X Z)

/-- The generic-point residue-field coproduct of a reduced
irreducible-component subscheme over a field is quasi-separated. -/
instance instCoproductQuasiSeparated
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (Z : irreducibleComponents X.left) :
    QuasiSeparated (genericPointSpectrumCoproductTo
      (X.left.irreducibleComponentSubscheme Z)) :=
  @Normalization.GenericPoints.instCoproductQuasiSeparated k _
    (Over.mk (X.left.irreducibleComponentSubschemeι Z ≫ X.hom))
    (IrreducibleComponent.instLocallyOfFiniteType X Z)

end GenericPoints
end IrreducibleComponent

end AlgebraicGeometry.SchemeOverField.Normalization
