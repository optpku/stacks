/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap91.Lemma_91_4_4_Obstruction
public import stacks_project.Chap91.Lemma_91_5_3_Lift
public import stacks_project.Chap91.Lemma_91_5_6
public import stacks_project.Chap91.Lemma_91_6_1_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat lifts along a strict flat first-order thickening

In Situation 91.3.1, if `(f, f')` is strict, `f'` is flat, and `F` is flat over `S`
(which forces `ℐ = f^* 𝒥`), a flat `𝒪_{X'}`-lift of `F` exists iff the relative
identity obstruction in `Ext F (f^* 𝒥 ⊗ F) 2` vanishes. Isomorphism classes of lifts
are then a principal homogeneous space under `Ext F (f^* 𝒥 ⊗ F) 1`, and automorphisms
of a given lift pulling back to `id_F` are canonically `Ext F (f^* 𝒥 ⊗ F) 0`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian (Ext)
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Hom.ModuleMap (Lift)
open AlgebraicGeometry.RingedSpace.Modules
open AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Hom
namespace FlatLift

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
variable {g : T ⟶ U} {F : T.left.Modules}

/-- Lemma 91.6.1 (1) In the situation above. There exists an `𝒪_{X'}`-module `F'` flat over
`S'` with `i^* F' ≅ F`, if and only if the class `o(F, f^* 𝒥 ⊗ F, 1)` in
`Ext F (f^* 𝒥 ⊗ F) 2` of Lemma 91.4.4 is zero. -/
@[stacks 08VR]
theorem exists_iff [SheafOfModules.IsFlatOver F g.left] [RingedSpace.Hom.IsFlat g.right]
    (hg : IsStrict g) [HasExt.{u} T.left.Modules] :
    Nonempty (FlatLift g F) ↔
      existenceObstruction T.hom F ((g.left^*).obj (idealModule U.hom) ⊗ F)
        (relativeIdentityInfinitesimalMap g hg F) = 0 := sorry

/-- Lemma 91.6.1 (2) If such a module exists, then the set of isomorphism classes of lifts
is principal homogeneous under `Ext F (f^* 𝒥 ⊗ F) 1`. The acting group is
`ExtensionClass (f^* 𝒥 ⊗ F) F`, identified with `Ext F (f^* 𝒥 ⊗ F) 1` by
`ExtensionClass.toExt`; the existence hypothesis is the basepoint `L0`, transported to
the 08L4 sequence with infinitesimal map `c = 1` and coefficients `f^* 𝒥 ⊗ F`. -/
@[stacks 08VR]
def sourceIdealIsoClassEquiv (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    [RingedSpace.Hom.IsFlat g.right] (L0 : FlatLift g F) :
    ExtensionClass ((g.left^*).obj (idealModule U.hom) ⊗ F) F ≃
      IsoClass T.hom F ((g.left^*).obj (idealModule U.hom) ⊗ F)
        (relativeIdentityInfinitesimalMap g hg F) :=
  @InfinitesimalExtension.isoClassEquiv T.left T.right T.hom
    ‹IsFirstOrderThickening T.hom› F ((g.left^*).obj (idealModule U.hom) ⊗ F)
    (relativeIdentityInfinitesimalMap g hg F) (toRelativeInfinitesimalExtension hg L0)

/-- The based chart sends an `𝒪_X`-extension class `ξ` to the translate of the basepoint. -/
theorem sourceIdealIsoClassEquiv_apply (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] [RingedSpace.Hom.IsFlat g.right]
    (L0 : FlatLift g F)
    (ξ : ExtensionClass ((g.left^*).obj (idealModule U.hom) ⊗ F) F) :
    sourceIdealIsoClassEquiv hg L0 ξ =
      @InfinitesimalExtension.vadd T.left T.right T.hom ‹IsFirstOrderThickening T.hom› F
        ((g.left^*).obj (idealModule U.hom) ⊗ F)
        (relativeIdentityInfinitesimalMap g hg F) ξ
        (IsoClass.mk (toRelativeInfinitesimalExtension hg L0) :
          IsoClass T.hom F ((g.left^*).obj (idealModule U.hom) ⊗ F)
            (relativeIdentityInfinitesimalMap g hg F)) := sorry

/-- The zero extension class is sent to the class of the associated relative 08L4 extension. -/
theorem sourceIdealIsoClassEquiv_zero (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] [RingedSpace.Hom.IsFlat g.right]
    (L0 : FlatLift g F) :
    sourceIdealIsoClassEquiv hg L0 0 =
      IsoClass.mk (toRelativeInfinitesimalExtension hg L0) := sorry

/-- The inverse chart is torsor subtraction against the basepoint. -/
theorem sourceIdealIsoClassEquiv_symm_apply (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] [RingedSpace.Hom.IsFlat g.right]
    (L0 : FlatLift g F)
    (p : IsoClass T.hom F ((g.left^*).obj (idealModule U.hom) ⊗ F)
      (relativeIdentityInfinitesimalMap g hg F)) :
    (sourceIdealIsoClassEquiv hg L0).symm p =
      @InfinitesimalExtension.vsub T.left T.right T.hom ‹IsFirstOrderThickening T.hom› F
        ((g.left^*).obj (idealModule U.hom) ⊗ F)
        (relativeIdentityInfinitesimalMap g hg F) p
        (IsoClass.mk (toRelativeInfinitesimalExtension hg L0) :
          IsoClass T.hom F ((g.left^*).obj (idealModule U.hom) ⊗ F)
            (relativeIdentityInfinitesimalMap g hg F)) := sorry

/-- The identity map of a lifted module, as a lift of `𝟙`. -/
def identityLift (L : FlatLift g F) :
    Lift L.module L.module (𝟙 ((T.hom^*).obj L.module)) where
  hom := 𝟙 L.module
  restrict := sorry

/-- The underlying middle map of `identityLift` is the identity. -/
theorem identityLift_hom (L : FlatLift g F) :
    (identityLift L).hom = 𝟙 L.module := sorry

/-- Automorphisms of a flat lift that pull back to `id_F` are the lifts of `𝟙` on `i^* F'`. -/
def idLiftHomEquiv (L : FlatLift g F) :
    Lift L.module L.module (𝟙 ((T.hom^*).obj L.module)) ≃
      Hom L L where
  toFun φ' := Hom.of φ'.hom sorry
  invFun ψ := Lift.of ψ.hom sorry
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `idLiftHomEquiv` is `Hom.of` on the underlying middle map. -/
theorem idLiftHomEquiv_apply (L : FlatLift g F)
    (φ' : Lift L.module L.module (𝟙 ((T.hom^*).obj L.module))) :
    (idLiftHomEquiv L φ').hom = φ'.hom := sorry

/-- Transport an `𝒪_X`-map `F ⟶ f^* 𝒥 ⊗ F` to `i^* F' ⟶ i^* F' ⊗ f^* 𝒥` along `α` and
the braiding. -/
def autHomEquiv (L : FlatLift g F) :
    (F ⟶ (g.left^*).obj (idealModule U.hom) ⊗ F) ≃
      ((T.hom^*).obj L.module ⟶
        (T.hom^*).obj L.module ⊗ (g.left^*).obj (idealModule U.hom)) :=
  (L.restrictIso.symm.homCongr
      (tensorIso (Iso.refl ((g.left^*).obj (idealModule U.hom))) L.restrictIso.symm)).trans
    ((Iso.refl ((T.hom^*).obj L.module)).homCongr (sourceIdealBraid ((T.hom^*).obj L.module)))

/-- The forward map of `autHomEquiv` conjugates by `α⁻¹` and `sourceIdealBraid`. -/
theorem autHomEquiv_apply (L : FlatLift g F)
    (α : F ⟶ (g.left^*).obj (idealModule U.hom) ⊗ F) :
    autHomEquiv L α =
      (Iso.refl ((T.hom^*).obj L.module)).homCongr (sourceIdealBraid ((T.hom^*).obj L.module))
        (L.restrictIso.symm.homCongr
          (tensorIso (Iso.refl ((g.left^*).obj (idealModule U.hom))) L.restrictIso.symm) α) :=
  sorry

/-- Lemma 91.6.1 (3) Given a lift `F'`, the set of automorphisms of `F'` which pull back to
`id_F` is canonically isomorphic to `Ext F (f^* 𝒥 ⊗ F) 0`. The identification is
`Ext.homEquiv₀`, transported along `α` and the braiding to
`Hom(i^* F', i^* F' ⊗ f^* 𝒥)`, then along `relativePerturbEquiv` at `φ = 𝟙`. -/
@[stacks 08VR]
def autEquiv (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    [RingedSpace.Hom.IsFlat g.right] (L : FlatLift g F) [HasExt.{u} T.left.Modules] :
    Ext F ((g.left^*).obj (idealModule U.hom) ⊗ F) 0 ≃ Hom L L :=
  Ext.homEquiv₀.trans <|
    (autHomEquiv L).trans <|
      (@ModuleMap.relativePerturbEquiv _ _ _ _ g L.module L.module
          (𝟙 ((T.hom^*).obj L.module)) (isIso_sourceIdealMulMap hg L)
          (identityLift L)).trans
        (idLiftHomEquiv L)

/-- The forward map of `autEquiv` sends an `Ext 0` class to the relative perturbation of
the identity lift. -/
theorem autEquiv_apply (hg : IsStrict g) [SheafOfModules.IsFlatOver F g.left]
    [RingedSpace.Hom.IsFlat g.right] (L : FlatLift g F) [HasExt.{u} T.left.Modules]
    (e : Ext F ((g.left^*).obj (idealModule U.hom) ⊗ F) 0) :
    autEquiv hg L e =
      idLiftHomEquiv L
        (ModuleMap.relativePerturb g (autHomEquiv L (Ext.homEquiv₀ e)) (identityLift L)) :=
  sorry

end FlatLift
end Hom
end AlgebraicGeometry.RingedSpace.Thickening
