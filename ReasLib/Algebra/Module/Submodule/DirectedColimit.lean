/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Colimits of directed submodule families

This leaf packages the canonical filtered diagram of a directed family of
submodules and its union cocones.  It is independent of ideal powers: a
specialized filtration supplies the family and its monotonicity. The universal
properties require the index order itself to be directed; directedness of the
image family alone does not ensure compatibility between incomparable indices.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v

namespace Submodule

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {ι : Type*} [Preorder ι]

/-- The `ModuleCat R` diagram of a monotone family of submodules, with maps given by subtype
inclusions.  A consumer supplies the family-specific monotonicity proof; no auxiliary instances
or local choices are needed. -/
noncomputable def directedDiagram (S : ι → Submodule R M)
    (hS : ∀ i j, i ≤ j → S i ≤ S j) : ι ⥤ ModuleCat.{v} R where
  obj i := ModuleCat.of R (S i)
  map f := ModuleCat.ofHom (Submodule.inclusion (hS _ _ (leOfHom f)))
  map_id := sorry
  map_comp := sorry

/-- The cocone into the ambient module induced by the subtype inclusions of a monotone family. -/
noncomputable def directedCocone (S : ι → Submodule R M)
    (hS : ∀ i j, i ≤ j → S i ≤ S j) : Cocone (directedDiagram S hS) where
  pt := ModuleCat.of R M
  ι :=
    { app := fun i ↦ ModuleCat.ofHom (S i).subtype
      naturality := fun i j f ↦ sorry }

/-- The cocone whose point is the supremum of the directed submodule family. -/
noncomputable def directedSupCocone (S : ι → Submodule R M)
    (hS : ∀ i j, i ≤ j → S i ≤ S j) : Cocone (directedDiagram S hS) where
  pt := ModuleCat.of R ((⨆ i, S i) : Submodule R M)
  ι :=
    { app := fun i ↦ ModuleCat.ofHom (Submodule.inclusion (le_iSup S i))
      naturality := fun i j f ↦ sorry }

section UniversalProperty

/-- The canonical descent from a directed submodule union. Its underlying map uses the
direct-limit lift and the inverse of the canonical bijection to the supremum. -/
noncomputable def directedSupDesc [IsDirectedOrder ι] (S : ι → Submodule R M)
    (hS : ∀ i j, i ≤ j → S i ≤ S j) (s : Cocone (directedDiagram S hS)) :
    (directedSupCocone S hS).pt ⟶ s.pt := by
  classical
  let transition : ∀ i j, i ≤ j → S i →ₗ[R] S j :=
    fun i j hij ↦ Submodule.inclusion (hS i j hij)
  let toSup : Module.DirectLimit (fun i ↦ S i) transition →ₗ[R]
      (⨆ i, S i : Submodule R M) :=
    Module.DirectLimit.lift R ι (fun i ↦ S i) transition
      (fun i ↦ Submodule.inclusion (le_iSup S i)) (fun _ _ _ _ ↦ rfl)
  have hbijective : Function.Bijective toSup := by sorry
  exact ModuleCat.ofHom
    ((Module.DirectLimit.lift R ι (fun i ↦ S i) transition
      (fun i ↦ (s.ι.app i).hom) (by sorry)).comp
        (LinearEquiv.ofBijective toSup hbijective).symm.toLinearMap)

/-- Descent from a directed union restricts to the specified map on every stage. -/
@[reassoc (attr := simp)]
theorem directedSupDesc_ι [IsDirectedOrder ι] (S : ι → Submodule R M)
    (hS : ∀ i j, i ≤ j → S i ≤ S j) (s : Cocone (directedDiagram S hS)) (i : ι) :
    (directedSupCocone S hS).ι.app i ≫ directedSupDesc S hS s = s.ι.app i := sorry

/-- A monotone submodule diagram indexed by a directed order has its supremum as colimit.
The empty index order is allowed: its supremum and colimit are both the zero module. -/
noncomputable def directedSupCocone_isColimit [IsDirectedOrder ι] (S : ι → Submodule R M)
    (hS : ∀ i j, i ≤ j → S i ≤ S j) :
    IsColimit (directedSupCocone S hS) where
  desc := directedSupDesc S hS
  fac := directedSupDesc_ι S hS
  uniq := sorry

/-- If the directed supremum is top, the ambient-module cocone is a colimit. -/
noncomputable def directedCocone_isColimit [IsDirectedOrder ι] (S : ι → Submodule R M)
    (hS : ∀ i j, i ≤ j → S i ≤ S j)
    (htop : (⨆ i, S i) = ⊤) :
    IsColimit (directedCocone S hS) where
  desc s := ModuleCat.ofHom
    ((directedSupDesc S hS s).hom.comp (LinearEquiv.ofTop (⨆ i, S i) htop).symm.toLinearMap)
  fac := sorry
  uniq := sorry

/-- The canonical colimit isomorphism from a directed submodule diagram to its ambient module,
when the directed supremum is top. -/
noncomputable def directedColimitIso [IsDirectedOrder ι] (S : ι → Submodule R M)
    (hS : ∀ i j, i ≤ j → S i ≤ S j)
    (htop : (⨆ i, S i) = ⊤)
    [HasColimit (directedDiagram S hS)] :
    colimit (directedDiagram S hS) ≅ ModuleCat.of R M :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit (directedDiagram S hS))
    (directedCocone_isColimit S hS htop)

/-- The colimit isomorphism restricts on every stage to the ambient subtype inclusion. -/
@[reassoc]
theorem directedColimitIso_hom_ι [IsDirectedOrder ι] (S : ι → Submodule R M)
    (hS : ∀ i j, i ≤ j → S i ≤ S j)
    (htop : (⨆ i, S i) = ⊤)
    [HasColimit (directedDiagram S hS)] (i : ι) :
    colimit.ι (directedDiagram S hS) i ≫
        (directedColimitIso S hS htop).hom =
      ModuleCat.ofHom (S i).subtype := sorry

end UniversalProperty

end Submodule
