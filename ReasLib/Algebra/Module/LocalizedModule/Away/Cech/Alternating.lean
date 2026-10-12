/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.CechNerve
public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Extended alternating Cech complexes of principal localizations

This module defines the ordinary alternating Cech complex attached to the canonical family of
principal localizations, its degree-zero augmentation, and the resulting extended complex.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicTopology

universe u v

namespace LocalizedModule.Away.Cech.Alternating

variable {R : Type u} [CommRing R]
variable {r : ℕ}

/-- The ordinary alternating Cech complex of an `R`-module for a finite family of principal
localizations. -/
@[stacks 0G6G "ordinary alternating Cech complex"]
abbrev complex (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] :
    CochainComplex (ModuleCat.{max u v} R) ℕ :=
  (alternatingCofaceMapComplex (ModuleCat.{max u v} R)).obj
    ((Arrow.mk (ModuleCat.ofHom (LocalizedModule.Away.Cech.familyMap M f))).cechConerve)

/-- The degree-zero map from an `R`-module into its ordinary alternating Cech complex. -/
@[stacks 0G6G "degree-zero alternating Cech augmentation map"]
abbrev augmentationMap
    (f : Fin r → R) (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    ModuleCat.of R M ⟶ (complex f M).X 0 :=
  (Arrow.mk (ModuleCat.ofHom (LocalizedModule.Away.Cech.familyMap M f))).augmentedCechConerve.hom.app
    (SimplexCategory.mk 0)

/-- The first differential is the alternating difference of the two degree-one cofaces. -/
@[stacks 0G6G "first differential of the alternating Cech complex"]
theorem d_zero_one
    (f : Fin r → R) (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    (complex f M).d 0 1 =
      ((Arrow.mk (ModuleCat.ofHom
        (LocalizedModule.Away.Cech.familyMap M f))).cechConerve).δ 0 -
        ((Arrow.mk (ModuleCat.ofHom
          (LocalizedModule.Away.Cech.familyMap M f))).cechConerve).δ 1 := sorry

/-- The augmentation followed by the first coface is the degree-one augmentation component. -/
@[stacks 0G6G "alternating Cech augmentation and first coface"]
theorem augmentationMap_comp_coface_zero
    (f : Fin r → R) (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    augmentationMap f M ≫
      ((Arrow.mk (ModuleCat.ofHom
        (LocalizedModule.Away.Cech.familyMap M f))).cechConerve).δ 0 =
        (Arrow.mk (ModuleCat.ofHom
          (LocalizedModule.Away.Cech.familyMap M f))).augmentedCechConerve.hom.app
            (SimplexCategory.mk 1) := sorry

/-- The augmentation followed by the second coface is the degree-one augmentation component. -/
@[stacks 0G6G "alternating Cech augmentation and second coface"]
theorem augmentationMap_comp_coface_one
    (f : Fin r → R) (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    augmentationMap f M ≫
      ((Arrow.mk (ModuleCat.ofHom
        (LocalizedModule.Away.Cech.familyMap M f))).cechConerve).δ 1 =
        (Arrow.mk (ModuleCat.ofHom
          (LocalizedModule.Away.Cech.familyMap M f))).augmentedCechConerve.hom.app
            (SimplexCategory.mk 1) := sorry

/-- The degree-zero augmentation is a cocycle in the ordinary alternating Cech complex. -/
@[stacks 0G6G "alternating Cech augmentation is a cocycle"]
theorem augmentationMap_comp_d_zero_one
    (f : Fin r → R) (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    augmentationMap f M ≫
      (complex f M).d 0 1 = 0 := sorry

/-- The canonical augmentation from an `R`-module in degree zero to its alternating Cech
complex. -/
@[stacks 0G6G "augmentation of the alternating Cech complex"]
abbrev augmentation
    (f : Fin r → R) (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    (CochainComplex.single₀ (ModuleCat.{max u v} R)).obj (ModuleCat.of R M) ⟶
      complex f M :=
  (CochainComplex.fromSingle₀Equiv (complex f M) (ModuleCat.of R M)).symm
    ⟨augmentationMap f M, augmentationMap_comp_d_zero_one f M⟩

/-- The extended alternating Cech complex attached to a finite family `f : Fin r → R` and an
`R`-module `M`. -/
@[stacks 0G6G "extended alternating Cech complex"]
def extended (f : Fin r → R) (M : Type (max u v))
    [AddCommGroup M] [Module R M] :
    CochainComplex (ModuleCat.{max u v} R) ℕ :=
  CochainComplex.fromSingle₀AsComplex (complex f M) (ModuleCat.of R M)
    (augmentation f M)

end LocalizedModule.Away.Cech.Alternating

end
