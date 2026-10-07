module

public import stacks_project.Chap66.Lemma_66_20_2_VanishingOpen

/-!
# Largest vanishing open of a local section on `X_spaces,étale`

A local section of an abelian sheaf on the étale site of algebraic spaces over `X`
vanishes on a unique largest open subspace of its domain, characterized by restriction
along spaces-étale arrows and by vanishing of geometric germs.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.20.2 (1): `sectionVanishingSet F U σ` is the largest open of `|U|` on which the
local section `σ` restricts to `0`. Equivalently, restriction of `σ` to an open subspace
`W ⊂ U` vanishes if and only if `W.pointsSet ⊆ sectionVanishingSet F U σ`. -/
@[stacks 04K9]
theorem sectionRestrict_eq_zero_iff_pointsSet_subset {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) (W : OpenSubspace U.left) :
    sectionRestrict F (openSubspaceHom U W) σ = 0 ↔
      W.pointsSet ⊆ sectionVanishingSet F U σ :=
  sorry

/-- Lemma 66.20.2 (2): for every morphism `φ : V ⟶ U` in `X_spaces,étale`, the restriction
`σ |_ V` vanishes if and only if the image `φ(V) ⊂ |U|` is contained in
`sectionVanishingSet F U σ`. -/
@[stacks 04K9]
theorem sectionRestrict_eq_zero_iff_range_subset {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) {V : spacesEtaleSite X} (φ : V ⟶ U) :
    sectionRestrict F φ σ = 0 ↔
      Set.range (Points.map φ.left) ⊆ sectionVanishingSet F U σ :=
  sorry

/-- Lemma 66.20.2 (3): for every geometric point `ū` of `U`, the germ `(U, ū, σ)` vanishes
in `F_x̄` if and only if `ū` lies in `sectionVanishingSet F U σ`, where
`x̄ = (U ⟶ X) ∘ ū`. -/
@[stacks 04K9]
theorem sectionGerm_eq_zero_iff_mem {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) (ubar : GeometricPoint U.left) :
    sectionGerm F U σ ubar = sectionGerm_zero F U ubar ↔
      ubar.image ∈ sectionVanishingSet F U σ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
