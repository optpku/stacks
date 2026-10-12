/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Colimits of directed submodule families

This leaf packages the canonical filtered diagram of a directed family of
submodules and its union cocones.  It is independent of ideal powers: a
specialized filtration should supply only the family and its monotonicity.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v

namespace Submodule

variable {R : Type u} [CommRing R]
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

/-- The directed supremum cocone is a colimit.  This is the reusable union-of-submodules
universal property; downstream constructions should use it instead of rebuilding a
`Module.DirectLimit` lift and its uniqueness proof. -/
noncomputable def directedSupCocone_isColimit (S : ι → Submodule R M)
    (hS : ∀ i j, i ≤ j → S i ≤ S j)
    (hdir : Directed (· ≤ ·) S) :
    IsColimit (directedSupCocone S hS) := sorry

/-- If the directed supremum is top, the ambient-module cocone is a colimit. -/
noncomputable def directedCocone_isColimit (S : ι → Submodule R M)
    (hS : ∀ i j, i ≤ j → S i ≤ S j)
    (hdir : Directed (· ≤ ·) S)
    (htop : (⨆ i, S i) = ⊤) :
    IsColimit (directedCocone S hS) := sorry

/-- The canonical colimit isomorphism from a directed submodule diagram to its ambient module,
when the directed supremum is top. -/
noncomputable def directedColimitIso (S : ι → Submodule R M)
    (hS : ∀ i j, i ≤ j → S i ≤ S j)
    (hdir : Directed (· ≤ ·) S)
    (htop : (⨆ i, S i) = ⊤)
    [HasColimit (directedDiagram S hS)] :
    colimit (directedDiagram S hS) ≅ ModuleCat.of R M :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit (directedDiagram S hS))
    (directedCocone_isColimit S hS hdir htop)

/-- The colimit isomorphism restricts on every stage to the ambient subtype inclusion. -/
@[reassoc]
theorem directedColimitIso_hom_ι (S : ι → Submodule R M)
    (hS : ∀ i j, i ≤ j → S i ≤ S j)
    (hdir : Directed (· ≤ ·) S)
    (htop : (⨆ i, S i) = ⊤)
    [HasColimit (directedDiagram S hS)] (i : ι) :
    colimit.ι (directedDiagram S hS) i ≫
        (directedColimitIso S hS hdir htop).hom =
      ModuleCat.ofHom (S i).subtype := sorry

end Submodule
