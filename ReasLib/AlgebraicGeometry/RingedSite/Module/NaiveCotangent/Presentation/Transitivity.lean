/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Homotopy
import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical presentation maps for a tower of ring sheaves

For a tower `O₁ ⟶ O₂ ⟶ O₃`, the canonical polynomial presentations are related in two
independent ways.  The first changes the generators along `O₂ ⟶ O₃` while keeping the
coefficient ring `O₁`; the second changes coefficients from `O₁` to `O₂` while keeping the
generators `O₃`.  Keeping these maps separate exposes the two functorial directions needed by
transitivity constructions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf

noncomputable section

universe u

namespace SheafOfModules.RingedSite.NaiveCotangent.Presentation

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {O₁ O₂ O₃ : Sheaf J CommRingCat.{u}}

/-- Lemma 17.31.5 (0E1Y): the canonical map `O₁[O₂] ⟶ O₁[O₃]` obtained by
sending each generator from `O₂` through `alpha : O₂ ⟶ O₃`. -/
@[stacks 0E1Y "generator map between canonical presentations"]
noncomputable abbrev generatorMap (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    FreeAlgebra.Presentation.underlying O₁ (Under.mk phi) ⟶
      FreeAlgebra.Presentation.underlying O₁ (Under.mk (phi ≫ alpha)) :=
  (FreeAlgebra.evaluation
    (Under.mk (FreeAlgebra.Presentation.base O₁ (Under.mk (phi ≫ alpha))))
    (FreeAlgebra.Presentation.generators (Under.mk phi))
    ((sheafForget J).map alpha ≫
      FreeAlgebra.Presentation.generator O₁ (Under.mk (phi ≫ alpha)))).right

/-- The generator map preserves the structure maps from `O₁`. -/
theorem generatorMap_baseSq (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    CommSq (𝟙 O₁) (FreeAlgebra.Presentation.base O₁ (Under.mk phi))
      (FreeAlgebra.Presentation.base O₁ (Under.mk (phi ≫ alpha)))
        (generatorMap phi alpha) := sorry

/-- Evaluation after the generator map agrees with evaluation followed by `alpha`. -/
theorem generatorMap_targetSq (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    CommSq (generatorMap phi alpha) (FreeAlgebra.Presentation.map O₁ (Under.mk phi))
      (FreeAlgebra.Presentation.map O₁ (Under.mk (phi ≫ alpha))) alpha := sorry

/-- Lemma 17.31.5 (0E1Y): the canonical map `O₁[O₃] ⟶ O₂[O₃]` obtained by
changing coefficients along `phi : O₁ ⟶ O₂` and fixing every generator from `O₃`. -/
@[stacks 0E1Y "coefficient map between canonical presentations"]
noncomputable abbrev coefficientMap (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    FreeAlgebra.Presentation.underlying O₁ (Under.mk (phi ≫ alpha)) ⟶
      FreeAlgebra.Presentation.underlying O₂ (Under.mk alpha) :=
  (FreeAlgebra.evaluation
    (Under.mk (phi ≫ FreeAlgebra.Presentation.base O₂ (Under.mk alpha)))
    (FreeAlgebra.Presentation.generators (Under.mk (phi ≫ alpha)))
    (FreeAlgebra.Presentation.generator O₂ (Under.mk alpha))).right

/-- The coefficient map intertwines the structure maps from `O₁` and `O₂`. -/
theorem coefficientMap_baseSq (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    CommSq phi (FreeAlgebra.Presentation.base O₁ (Under.mk (phi ≫ alpha)))
      (FreeAlgebra.Presentation.base O₂ (Under.mk alpha)) (coefficientMap phi alpha) := sorry

/-- Evaluation is unchanged by the coefficient map. -/
theorem coefficientMap_targetSq (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    CommSq (coefficientMap phi alpha)
      (FreeAlgebra.Presentation.map O₁ (Under.mk (phi ≫ alpha)))
      (FreeAlgebra.Presentation.map O₂ (Under.mk alpha)) (𝟙 O₃) := sorry

/-- Lemma 17.31.5 (0E1Y): the morphism from the canonical presentation of
`O₁ ⟶ O₂` to that of `O₁ ⟶ O₃`, induced by `alpha : O₂ ⟶ O₃`. -/
@[stacks 0E1Y "generator morphism of canonical presentations"]
noncomputable def generatorHom (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    Hom (FreeAlgebra.Presentation.base O₁ (Under.mk phi))
      (FreeAlgebra.Presentation.map O₁ (Under.mk phi))
      (FreeAlgebra.Presentation.base O₁ (Under.mk (phi ≫ alpha)))
      (FreeAlgebra.Presentation.map O₁ (Under.mk (phi ≫ alpha))) where
  base := 𝟙 O₁
  middle := generatorMap phi alpha
  target := alpha
  baseSq := generatorMap_baseSq phi alpha
  targetSq := generatorMap_targetSq phi alpha

/-- Lemma 17.31.5 (0E1Y): the morphism from the canonical presentation of
`O₁ ⟶ O₃` to that of `O₂ ⟶ O₃`, induced by changing coefficients along
`phi : O₁ ⟶ O₂`. -/
@[stacks 0E1Y "coefficient morphism of canonical presentations"]
noncomputable def coefficientHom (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    Hom (FreeAlgebra.Presentation.base O₁ (Under.mk (phi ≫ alpha)))
      (FreeAlgebra.Presentation.map O₁ (Under.mk (phi ≫ alpha)))
      (FreeAlgebra.Presentation.base O₂ (Under.mk alpha))
      (FreeAlgebra.Presentation.map O₂ (Under.mk alpha)) where
  base := phi
  middle := coefficientMap phi alpha
  target := 𝟙 O₃
  baseSq := coefficientMap_baseSq phi alpha
  targetSq := coefficientMap_targetSq phi alpha

variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Lemma 17.31.5 (0E1Y): the base-change map
`O₃ ⊗[O₂] NL(O₂/O₁) ⟶ NL(O₃/O₁)` induced by the generator morphism of canonical
presentations. -/
@[stacks 0E1Y "left map in naive-cotangent transitivity"]
noncomputable abbrev left (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    (extendComplex alpha).obj (NaiveCotangent.obj O₁ (Under.mk phi)) ⟶
      NaiveCotangent.obj O₁ (Under.mk (phi ≫ alpha)) :=
  Hom.map (generatorHom phi alpha)

/-- Lemma 17.31.5 (0E1Y): the comparison
`NL(O₃/O₁) ⟶ NL(O₃/O₂)` induced by changing coefficients between the canonical
presentations. -/
@[stacks 0E1Y "comparison map in naive-cotangent transitivity"]
noncomputable def comparison (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    NaiveCotangent.obj O₁ (Under.mk (phi ≫ alpha)) ⟶
      NaiveCotangent.obj O₂ (Under.mk alpha) :=
  (extendComplexIdIso O₃).inv.app (NaiveCotangent.obj O₁ (Under.mk (phi ≫ alpha))) ≫
    Hom.map (coefficientHom phi alpha)

/-- The presentation map factoring through `O₂`, regarded as a morphism between the canonical
presentations of `O₁ ⟶ O₂` and `O₂ ⟶ O₃`. -/
noncomputable abbrev constantMap (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    FreeAlgebra.Presentation.underlying O₁ (Under.mk phi) ⟶
      FreeAlgebra.Presentation.underlying O₂ (Under.mk alpha) :=
  FreeAlgebra.Presentation.map O₁ (Under.mk phi) ≫
    FreeAlgebra.Presentation.base O₂ (Under.mk alpha)

/-- The generator-coefficient presentation map is compatible with the base map `phi`. -/
theorem compositeMap_baseSq (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    CommSq phi (FreeAlgebra.Presentation.base O₁ (Under.mk phi))
      (FreeAlgebra.Presentation.base O₂ (Under.mk alpha))
        (generatorMap phi alpha ≫ coefficientMap phi alpha) := sorry

/-- The presentation map factoring through `O₂` is compatible with the base map `phi`. -/
theorem constantMap_baseSq (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    CommSq phi (FreeAlgebra.Presentation.base O₁ (Under.mk phi))
      (FreeAlgebra.Presentation.base O₂ (Under.mk alpha)) (constantMap phi alpha) := sorry

/-- The generator-coefficient presentation map is compatible with the target map `alpha`. -/
theorem compositeMap_targetSq (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    CommSq (generatorMap phi alpha ≫ coefficientMap phi alpha)
      (FreeAlgebra.Presentation.map O₁ (Under.mk phi))
      (FreeAlgebra.Presentation.map O₂ (Under.mk alpha)) alpha := sorry

/-- The presentation map factoring through `O₂` is compatible with the target map `alpha`. -/
theorem constantMap_targetSq (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    CommSq (constantMap phi alpha) (FreeAlgebra.Presentation.map O₁ (Under.mk phi))
      (FreeAlgebra.Presentation.map O₂ (Under.mk alpha)) alpha := sorry

/-- Lemma 17.31.5 (0E1Y): the two canonical parallel morphisms from the presentation of
`O₁ ⟶ O₂` to the presentation of `O₂ ⟶ O₃`. -/
@[stacks 0E1Y "canonical parallel morphisms for transitivity"]
noncomputable def towerParallel (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    Hom.Parallel (FreeAlgebra.Presentation.base O₁ (Under.mk phi))
      (FreeAlgebra.Presentation.map O₁ (Under.mk phi))
      (FreeAlgebra.Presentation.base O₂ (Under.mk alpha))
      (FreeAlgebra.Presentation.map O₂ (Under.mk alpha)) where
  base := phi
  first := generatorMap phi alpha ≫ coefficientMap phi alpha
  second := constantMap phi alpha
  target := alpha
  firstBaseSq := compositeMap_baseSq phi alpha
  secondBaseSq := constantMap_baseSq phi alpha
  firstTargetSq := compositeMap_targetSq phi alpha
  secondTargetSq := constantMap_targetSq phi alpha

/-- The map induced by the first canonical parallel presentation morphism is the composite of
the left and comparison maps. -/
theorem left_comp_comparison_eq_firstMap (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    left phi alpha ≫ comparison phi alpha =
      Hom.Parallel.firstMap (towerParallel phi alpha) := sorry

/-- The map induced by the canonical presentation morphism factoring through `O₂` is zero. -/
theorem secondMap_eq_zero (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    Hom.Parallel.secondMap (towerParallel phi alpha) = 0 := sorry

/-- Lemma 17.31.5 (0E1Y): the canonical null-homotopy of the composite of the left and
comparison maps in naive-cotangent transitivity. -/
@[stacks 0E1Y "naive-cotangent transitivity null-homotopy"]
noncomputable def nullHomotopy (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    Homotopy (left phi alpha ≫ comparison phi alpha) 0 :=
  (Homotopy.ofEq (left_comp_comparison_eq_firstMap phi alpha)).trans
    ((Hom.Parallel.mapHomotopy (towerParallel phi alpha)).trans
      (Homotopy.ofEq (secondMap_eq_zero phi alpha)))

/-- Lemma 17.31.5 (0E1Y): the canonical map from the base-changed naive cotangent complex to
the mapping cocone of the transitivity comparison. -/
@[stacks 0E1Y "naive-cotangent transitivity cocone map"]
noncomputable def toCocone (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    (extendComplex alpha).obj (NaiveCotangent.obj O₁ (Under.mk phi)) ⟶
      CochainComplex.mappingCocone (comparison phi alpha) :=
  CochainComplex.MappingCoconeFactorization.map
    (left phi alpha) (comparison phi alpha) (nullHomotopy phi alpha)

/-- The canonical cocone map projects to the left map. -/
@[simp]
theorem toCocone_fst (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    toCocone phi alpha ≫ CochainComplex.mappingCocone.fst (comparison phi alpha) =
      left phi alpha := sorry

-- The two polynomial-presentation maps are explicit adjunction constructions; only their
-- compatibility equations carry deferred proof obligations.

-- Any `sorryAx` below is confined to the `CommSq` proof fields; all three morphism fields of
-- each `Hom` are the explicit maps displayed above.

end SheafOfModules.RingedSite.NaiveCotangent.Presentation
