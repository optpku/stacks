module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.Topology.LocallyClosed.Subsets
public import stacks_project.Chap59.Definition_59_31_3_EtaleSupport

/-!
# Étale sections supported in a locally closed subset

The groups `H_Z(F)` of small-étale abelian-sheaf sections whose support lies in
a locally closed subset `Z` of an étale `X`-scheme.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
variable {W : Scheme.{u}} (hW : W ⟶ X) [Etale hW]

/-- The group `H_Z(F)` of sections of an abelian sheaf `F` on an ambient Zariski
open `U` of an étale `X`-scheme `W`, whose étale section support is contained in
a locally closed subset `Z ⊆ W` that is closed in `U`. -/
def sectionsSupportedIn (Z : LocallyCloseds W) (U : W.Opens)
    (h_subset : (Z : Set W) ⊆ U)
    (h_closed : IsClosed (U.ι ⁻¹' (Z : Set W))) :
    AddSubgroup (F.1.obj (op (mk (U.ι ≫ hW)))) where
  carrier :=
    {σ | U.ι '' (abelianSheafSectionSupport F (mk (U.ι ≫ hW)) σ :
          Set (mk (U.ι ≫ hW)).left) ⊆ (Z : Set W)}
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- Membership in `H_Z(F)` is containment of the image of the étale section
support in `Z`. -/
theorem mem_sectionsSupportedIn_iff (Z : LocallyCloseds W) (U : W.Opens)
    (h_subset : (Z : Set W) ⊆ U)
    (h_closed : IsClosed (U.ι ⁻¹' (Z : Set W)))
    (σ : F.1.obj (op (mk (U.ι ≫ hW)))) :
    σ ∈ sectionsSupportedIn F hW Z U h_subset h_closed ↔
      U.ι '' (abelianSheafSectionSupport F (mk (U.ι ≫ hW)) σ :
          Set (mk (U.ι ≫ hW)).left) ⊆ (Z : Set W) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
