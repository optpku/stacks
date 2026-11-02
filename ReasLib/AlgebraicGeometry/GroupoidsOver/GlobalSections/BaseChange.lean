/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.PullbackSections
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec
public import ReasLib.RingTheory.RingHom.SquareZero

/-!
# Base change of a scheme and a module along morphisms over `Spec(Λ)`

For `w : W ⟶ Spec(Λ)` and `T ⟶ Spec(Λ)`, the base change is `W_T = T ×_{Spec(Λ)} W` and the
pullback module `F_T`, together with the affine specialisation `T = Spec(A)` and the
first-order thickening `W_A ⟶ W_{A'}` induced by a square-zero surjection `A' → A`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.GlobalSections

/-- Compatibility of `Spec(A) ⟶ Spec(Λ)` with a morphism of `Λ`-algebras `A' → A`. -/
theorem specOverMap_w (Λ A A' : Type u) [CommRing Λ] [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A] :
    Spec.map (CommRingCat.ofHom (algebraMap A' A)) ≫ (Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap Λ A'))).hom =
      (Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap Λ A))).hom :=
  by
    change Spec.map (CommRingCat.ofHom (algebraMap A' A)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ A')) =
        Spec.map (CommRingCat.ofHom (algebraMap Λ A))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq Λ A' A]

/-- The morphism `Spec(A) ⟶ Spec(A')` over `Spec(Λ)` induced by `algebraMap A' A`. -/
def specOverMap (Λ A A' : Type u) [CommRing Λ] [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A] :
    Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap Λ A)) ⟶ Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap Λ A')) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A' A))) (specOverMap_w Λ A A')

/-- The underlying scheme morphism of `specOverMap` is `Spec` of `algebraMap A' A`. -/
theorem specOverMap_left (Λ A A' : Type u) [CommRing Λ] [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A] :
    (specOverMap Λ A A').left = Spec.map (CommRingCat.ofHom (algebraMap A' A)) :=
  rfl

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable {W : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of Λ))

/-- The base change `W_T = T ×_S W`. -/
def baseChange (T : Over (Spec (CommRingCat.of Λ))) : Scheme.{u} :=
  pullback T.hom w

/-- The projection `W_T ⟶ T`. -/
def baseChangeFst (T : Over (Spec (CommRingCat.of Λ))) : baseChange w T ⟶ T.left :=
  pullback.fst T.hom w

/-- The projection `W_T ⟶ W`. -/
def baseChangeSnd (T : Over (Spec (CommRingCat.of Λ))) : baseChange w T ⟶ W :=
  pullback.snd T.hom w

/-- The morphism `W_{T'} ⟶ W_T` induced by a morphism `T' ⟶ T` over `S`. -/
def baseChangeMap {T T' : Over (Spec (CommRingCat.of Λ))} (f : T' ⟶ T) :
    baseChange w T' ⟶ baseChange w T :=
  pullback.map T'.hom w T.hom w f.left (𝟙 W) (𝟙 (Spec (CommRingCat.of Λ)))
    ((Category.comp_id T'.hom).trans (Over.w f).symm)
    ((Category.comp_id w).trans (Category.id_comp w).symm)

/-- The first projection of `baseChangeMap f` is `f` on the test schemes. -/
theorem baseChangeMap_fst {T T' : Over (Spec (CommRingCat.of Λ))} (f : T' ⟶ T) :
    baseChangeMap w f ≫ baseChangeFst w T = baseChangeFst w T' ≫ f.left :=
  pullback.lift_fst _ _ _

/-- The second projection of `baseChangeMap f` is the identity on `W`. -/
theorem baseChangeMap_snd {T T' : Over (Spec (CommRingCat.of Λ))} (f : T' ⟶ T) :
    baseChangeMap w f ≫ baseChangeSnd w T = baseChangeSnd w T' :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

variable (F : W.Modules)

/-- The pullback module `F_T` of `F` to `W_T`. -/
def modulePullback (T : Over (Spec (CommRingCat.of Λ))) : (baseChange w T).Modules :=
  (Scheme.Modules.pullback (baseChangeSnd w T)).obj F

/-- The comparison identifying `F_{T'}` with the pullback of `F_T` along `W_{T'} ⟶ W_T`. -/
def modulePullbackMap {T T' : Over (Spec (CommRingCat.of Λ))} (f : T' ⟶ T) :
    modulePullback w F T' ⟶
      (Scheme.Modules.pullback (baseChangeMap w f)).obj (modulePullback w F T) :=
  (Scheme.Modules.pullbackCongr (baseChangeMap_snd w f)).inv.app F ≫
    (Scheme.Modules.pullbackComp (baseChangeMap w f) (baseChangeSnd w T)).inv.app F

/-- The affine base change `W_A` of `W` along `Spec(A) ⟶ Spec(Λ)`. -/
abbrev affineBaseChange (A : Type u) [CommRing A] [Algebra Λ A] : Scheme.{u} :=
  baseChange w (Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap Λ A)))

/-- The affine pullback module `F_A` of `F` to `W_A`. -/
abbrev affineModulePullback (A : Type u) [CommRing A] [Algebra Λ A] :
    (affineBaseChange w A).Modules :=
  modulePullback w F (Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap Λ A)))

/-- The first-order thickening `W_A ⟶ W_{A'}` induced by `algebraMap A' A`. -/
def thickeningHom (A A' : Type u) [CommRing A] [CommRing A'] [Algebra Λ A] [Algebra Λ A']
    [Algebra A' A] [IsScalarTower Λ A' A] :
    affineBaseChange w A ⟶ affineBaseChange w A' :=
  baseChangeMap w (specOverMap Λ A A')

/-- `thickeningHom` is the base change of `Spec.map (algebraMap A' A)` along `W`. -/
theorem thickeningHom_eq (A A' : Type u) [CommRing A] [CommRing A'] [Algebra Λ A] [Algebra Λ A']
    [Algebra A' A] [IsScalarTower Λ A' A] :
    thickeningHom w A A' = baseChangeMap w (specOverMap Λ A A') :=
  rfl

/-- A square-zero extension of algebras induces a first-order thickening on spectra. -/
instance instIsFirstOrderThickening_specMap
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :
    IsFirstOrderThickening (Spec.map (CommRingCat.ofHom (algebraMap A' A))) :=
  by
    let f := CommRingCat.ofHom (algebraMap A' A)
    have hclosed : IsClosedImmersion (Spec.map f) :=
      IsClosedImmersion.spec_of_surjective f
        (RingHom.IsSquareZeroExtension.surjective (f := algebraMap A' A))
    letI := hclosed
    have hker : RingHom.ker (Spec.map f).appTop.hom =
        (RingHom.ker (algebraMap A' A)).comap (Scheme.ΓSpecIso (CommRingCat.of A')).hom.hom := by
      calc
        _ = RingHom.ker ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp
            (Spec.map f).appTop.hom) :=
          (RingHom.ker_comp_of_injective _
            (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1).symm
        _ = _ := by
          rw [← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp,
            ← RingHom.comap_ker]
          rfl
    have hpow : (Spec.map f).ker ^ 2 = 0 := by
      apply Scheme.IdealSheafData.ext_of_isAffine
      change ((Spec.map f).ker.ideal ⟨⊤, isAffineOpen_top _⟩) ^ 2 = ⊥
      rw [Scheme.Hom.ker_apply]
      change (RingHom.ker (Spec.map f).appTop.hom) ^ 2 = ⊥
      rw [hker]
      apply le_bot_iff.mp
      calc
        _ ≤ ((RingHom.ker (algebraMap A' A)) ^ 2).comap
            (Scheme.ΓSpecIso (CommRingCat.of A')).hom.hom := Ideal.le_comap_pow _ _
        _ = ⊥ := by
          rw [RingHom.IsSquareZeroExtension.ker_sq_eq_bot (f := algebraMap A' A)]
          exact Ideal.comap_bot_of_injective _
            (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A')).hom).1
    exact { isClosedImmersion := hclosed, ker_isNilpotent := ⟨2, hpow⟩, ker_pow_succ := hpow }

/-- The base change of a first-order thickening of spectra along `W` is a first-order thickening. -/
instance instIsFirstOrderThickening_baseChange
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra Λ A] [Algebra Λ A']
    [Algebra A' A] [IsScalarTower Λ A' A]
    [IsFirstOrderThickening (Spec.map (CommRingCat.ofHom (algebraMap A' A)))] :
    IsFirstOrderThickening (thickeningHom w A A') :=
  sorry

/-- Restriction of global sections of `F_T` along `T' ⟶ T`. -/
def sectionsRestrict {T T' : Over (Spec (CommRingCat.of Λ))} (f : T' ⟶ T) :
    Γ(modulePullback w F T, ⊤) → Γ(modulePullback w F T', ⊤) :=
  fun x ↦
    Scheme.Modules.globalSectionsMap ((Scheme.Modules.pullbackCongr (baseChangeMap_snd w f)).hom.app F)
      (Scheme.Modules.globalSectionsMap
        ((Scheme.Modules.pullbackComp (baseChangeMap w f)
            (baseChangeSnd w T)).hom.app F)
        ((Scheme.Modules.globalSectionsPullback (baseChangeMap w f)
            (modulePullback w F T)).hom x))

private theorem globalSectionsMap_pullbackCongr {X Y : Scheme.{u}}
    {f g : X ⟶ Y} (h : f = g) (G : Y.Modules) :
    Scheme.Modules.globalSectionsMap ((Scheme.Modules.pullbackCongr h).hom.app G) =
      eqToHom (congrArg
        (fun k ↦ Scheme.Modules.globalSections ((Scheme.Modules.pullback k).obj G)) h) := by
  subst g
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem sectionsRestrict_eq {T T' : Over (Spec (CommRingCat.of Λ))}
    (f : T' ⟶ T) :
    sectionsRestrict w F f =
      (Scheme.Modules.PullbackSections.map F
        (Over.homMk (U := Over.mk (baseChangeSnd w T'))
          (V := Over.mk (baseChangeSnd w T))
          (baseChangeMap w f) (baseChangeMap_snd w f))).hom := by
  unfold Scheme.Modules.PullbackSections.map Scheme.Modules.globalSectionsPullbackComp
  dsimp only
  rw [← globalSectionsMap_pullbackCongr]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restricting sections along an identity morphism is the identity function. -/
theorem sectionsRestrict_id (T : Over (Spec (CommRingCat.of Λ))) :
    sectionsRestrict w F (𝟙 T) = id := by
  have h : Over.homMk (U := Over.mk (baseChangeSnd w T))
      (V := Over.mk (baseChangeSnd w T))
      (baseChangeMap w (𝟙 T)) (baseChangeMap_snd w (𝟙 T)) =
      𝟙 (Over.mk (baseChangeSnd w T)) := by
    apply Over.OverMorphism.ext
    exact pullback.map_id
  rw [sectionsRestrict_eq, h, Scheme.Modules.PullbackSections.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of sections respects composition of morphisms over the base. -/
theorem sectionsRestrict_comp {T₁ T₂ T₃ : Over (Spec (CommRingCat.of Λ))}
    (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    sectionsRestrict w F (f ≫ g) = sectionsRestrict w F f ∘ sectionsRestrict w F g := by
  have h : Over.homMk (U := Over.mk (baseChangeSnd w T₁))
      (V := Over.mk (baseChangeSnd w T₃))
      (baseChangeMap w (f ≫ g)) (baseChangeMap_snd w (f ≫ g)) =
      Over.homMk (U := Over.mk (baseChangeSnd w T₁))
        (V := Over.mk (baseChangeSnd w T₂)) (baseChangeMap w f) (baseChangeMap_snd w f) ≫
        Over.homMk (U := Over.mk (baseChangeSnd w T₂))
          (V := Over.mk (baseChangeSnd w T₃))
          (baseChangeMap w g) (baseChangeMap_snd w g) := by
    apply Over.OverMorphism.ext
    change baseChangeMap w (f ≫ g) = baseChangeMap w f ≫ baseChangeMap w g
    apply pullback.hom_ext <;>
      simp [baseChangeMap, pullback.map, Category.assoc]
  rw [sectionsRestrict_eq, h, Scheme.Modules.PullbackSections.map_comp,
    sectionsRestrict_eq, sectionsRestrict_eq]
  rfl

end AlgebraicGeometry.GroupoidsOver.GlobalSections
