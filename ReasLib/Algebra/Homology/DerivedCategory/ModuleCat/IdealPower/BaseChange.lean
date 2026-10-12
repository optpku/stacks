/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.Algebra.Category.CommRingCat.IdealPower
public import ReasLib.Algebra.Category.ModuleCat.Sequential.Restriction
public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Module
public import ReasLib.Algebra.Homology.HomologicalComplex.ModIdeal.Change
public import ReasLib.Algebra.Homology.HomologicalComplex.ModIdeal.Homology
public import ReasLib.Algebra.Homology.ShortComplex.IdealPower
public import ReasLib.Algebra.Module.IdealPower.Quotient
public import ReasLib.Algebra.Module.IdealPower.System
public import ReasLib.CategoryTheory.Abelian.Projective.Ext.Linear

import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ext towers under flat base change

@stack 0EH0

This leaf owns the reusable tower data for Lemma 15.101.11.  The generic restriction
construction works for any sequential system of commutative rings equipped with compatible
maps from a fixed base ring.  The ideal-power specialization then exposes the ambient Ext
quotient tower, the reduced Ext stages, and the induced tower after restriction to the base.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite

noncomputable section

universe u v

namespace IadicFiniteModuleSystem.Ext.BaseChange

open CategoryTheory.SequentialInverseSystem
open CategoryTheory.Abelian

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-! ### The ideal-power base-change tower -/

/-- The extension of `I` to `B`. -/
@[stacks 0EH0 "ideal extension used in the Ext base-change tower"]
abbrev mappedIdeal (I : Ideal A) : Ideal B := Ideal.map (algebraMap A B) I

/-- The stage ring `B / (I B)^(n + 1)` in the positive-indexed base-change tower. -/
@[stacks 0EH0 "positive ideal-power base-change stage ring"]
abbrev quotientRing (I : Ideal A) (n : ℕ) : Type u :=
  (CommRingCat.IdealPower.Positive.stage
      (mappedIdeal (A := A) (B := B) I) n : Type u)

/-- The zero-based quotient-ring stage is the positive-indexed system stage at `n + 1`. -/
@[stacks 0EH0 "base-change quotient ring and positive stage ring"]
theorem quotientRing_eq_stageRing (I : Ideal A) (n : ℕ) :
    quotientRing (A := A) (B := B) I n =
      IadicFiniteModuleSystem.stageRing B (mappedIdeal (A := A) (B := B) I)
        (Nat.succPNat n) := sorry

/-- The transition ring map from stage `n + 1` to stage `n`. -/
@[stacks 0EH0 "positive ideal-power base-change ring transition"]
abbrev quotientRingStep (I : Ideal A) (n : ℕ) :
    quotientRing (A := A) (B := B) I (n + 1) →+* quotientRing (A := A) (B := B) I n :=
  (CommRingCat.IdealPower.Positive.step
      (mappedIdeal (A := A) (B := B) I) n).hom

/-- The commutative-ring system of positive ideal-power stages over `B`. -/
@[stacks 0EH0 "positive ideal-power base-change ring system"]
abbrev quotientRingSystem (I : Ideal A) :
  SequentialInverseSystem CommRingCat.{u} :=
  CommRingCat.IdealPower.Positive.system
    (mappedIdeal (A := A) (B := B) I)

/-- The canonical cone from `A` to the positive ideal-power quotient system of `B`. -/
@[stacks 0EH0 "base-ring cone over the ideal-power tower"]
def quotientCone (I : Ideal A) : Cone (quotientRingSystem (A := A) (B := B) I) :=
  (CommRingCat.IdealPower.Positive.cone
    (mappedIdeal (A := A) (B := B) I)).extend
      (CommRingCat.ofHom (algebraMap A B))

/-- The structure map from `A` to the `n`th quotient stage. -/
@[stacks 0EH0 "base-ring map into an ideal-power stage"]
abbrev quotientBaseMap (I : Ideal A) (n : ℕ) :
    A →+* quotientRing (A := A) (B := B) I n :=
  ((quotientCone (A := A) (B := B) I).stageMap n).hom

/-- Compatibility of the base-ring maps with the ideal-power transition maps. -/
@[stacks 0EH0 "compatibility of base maps with ideal-power transitions"]
theorem quotientBaseMap_compatibility (I : Ideal A) (n : ℕ) :
    quotientBaseMap (A := A) (B := B) I n =
      ((quotientRingSystem (A := A) (B := B) I).stepMap n).hom.comp
        (quotientBaseMap (A := A) (B := B) I (n + 1)) := sorry

/-- The base map to a quotient stage is the composite of `A ⟶ B` with the quotient map. -/
@[stacks 0EH0 "factorization of the base map to an ideal-power quotient"]
theorem quotientBaseMap_factor (I : Ideal A) (n : ℕ) :
    quotientBaseMap (A := A) (B := B) I n =
      (Ideal.Quotient.mk (mappedIdeal (A := A) (B := B) I ^ (n + 1))).comp
        (algebraMap A B) := sorry

/-- The `A`-module tower of ambient Ext groups modulo `(I B)^(n + 1)`. -/
@[stacks 0EH0 "ambient Ext quotient tower under flat base change"]
abbrev quotientExtTower (I : Ideal A) (M N : ModuleCat.{v} B) [Small.{v} B] (i : ℕ) :
    SequentialInverseSystem (ModuleCat.{v} A) :=
  (Ideal.PowerQuotient.positiveSystem (mappedIdeal (A := A) (B := B) I)
      (ModuleCat.of B (Ext M N i))) ⋙
    ModuleCat.restrictScalars (algebraMap A B)

/-- The quotient of a `B`-module by the `(n + 1)`st extended ideal power. -/
@[stacks 0EH0 "module reduction at an ideal-power base-change stage"]
abbrev reductionModule (I : Ideal A) (M : ModuleCat.{v} B) (n : ℕ) :
    ModuleCat.{v} (quotientRing (A := A) (B := B) I n) :=
  Ideal.PowerQuotient.stageOver (mappedIdeal (A := A) (B := B) I) M (n + 1)

/-- The reduced Ext stage over `B / (I B)^(n + 1)`. -/
@[stacks 0EH0 "reduced Ext stage over an ideal-power quotient ring"]
abbrev reductionExtStage (I : Ideal A) (M N : ModuleCat.{v} B) [Small.{v} B] (i n : ℕ) :
    ModuleCat.{v} (quotientRing (A := A) (B := B) I n) :=
  ModuleCat.of (quotientRing (A := A) (B := B) I n)
    (Ext (reductionModule I M n) (reductionModule I N n) i)

/-- Evaluation of a strict reduced Ext tower at stage `n` over its quotient ring. -/
@[stacks 0EH0 "quotient-ring evaluation of a reduced Ext tower"]
abbrev reductionEvaluation (I : Ideal A) (n : ℕ) :
    ModuleSystem.{u, v} (quotientRingSystem (A := A) (B := B) I) ⥤
      ModuleCat.{v} (quotientRing (A := A) (B := B) I n) :=
  evaluation (quotientRingSystem (A := A) (B := B) I) n

/-- Evaluation of a strict reduced Ext tower at stage `n`, restricted to `A`. -/
@[stacks 0EH0 "A-restricted evaluation of a reduced Ext tower"]
abbrev reductionEvaluationOverA (I : Ideal A) (n : ℕ) :
    ModuleSystem.{u, v} (quotientRingSystem (A := A) (B := B) I) ⥤
      ModuleCat.{v} A :=
  restrictEvaluation (quotientRingSystem (A := A) (B := B) I)
    (quotientCone (A := A) (B := B) I) n

/-- The `A`-module sequential tower obtained by restricting a strict reduced Ext tower. -/
@[stacks 0EH0 "A-restricted reduced Ext tower"]
noncomputable def reductionTowerOverA
    (I : Ideal A)
    (T : ModuleSystem.{u, v} (quotientRingSystem (A := A) (B := B) I)) :
  SequentialInverseSystem (ModuleCat.{v} A) :=
  restrictTower (quotientRingSystem (A := A) (B := B) I)
    (quotientCone (A := A) (B := B) I) T

/-! ### The quotient-Hom model attached to a resolution -/

namespace ResolutionModel

variable [Small.{v} B]
variable {M : ModuleCat.{v} B}
variable {F : ChainComplex (ModuleCat.{v} B) ℕ}
variable (π : F ⟶ ChainComplex.moduleSingle B M) [ChainComplex.IsFiniteFreeResolution π]

/-- The extended ideal power used at stage `n` of a resolution model. -/
@[stacks 0EH0 "ideal at a resolution-model stage"]
abbrev stageIdeal (I : Ideal A) (n : ℕ) : Ideal B :=
  mappedIdeal (A := A) (B := B) I ^ (n + 1)

/-- The stage ideal `(I B) ^ (n + 1)` is the image of `I ^ (n + 1)` under `A ⟶ B`. -/
@[stacks 0EH0 "ideal-power extension at a base-change stage"]
theorem stageIdeal_eq_map_pow (I : Ideal A) (n : ℕ) :
    stageIdeal (A := A) (B := B) I n =
      Ideal.map (algebraMap A B) (I ^ (n + 1)) := sorry

/-- The module-valued Hom complex of the chosen finite free resolution against `N`. -/
@[stacks 0EH0 "Hom complex of a chosen finite free resolution"]
abbrev homComplex (N : ModuleCat.{v} B) : CochainComplex (ModuleCat.{v} B) ℤ :=
  CochainComplex.HomComplex.moduleComplex B
    (ChainComplex.IsFreeResolution.toProjectiveResolution π).cochainComplex
    ((CochainComplex.singleFunctor (ModuleCat.{v} B) 0).obj N)

/-- The three-term degree-`i` window in the resolution Hom complex. -/
@[stacks 0EH0 "three-term window in a finite-free-resolution Hom complex"]
abbrev homWindow (N : ModuleCat.{v} B) (i : ℕ) :
    ShortComplex (ModuleCat.{v} B) :=
  (homComplex π N).sc (i : ℤ)

namespace HomWindow

/-- The left term of a finite-free-resolution Hom window is finite when the target is finite. -/
@[stacks 0EH0 "finiteness of the left Hom-window term"]
noncomputable instance finiteX₁ (N : ModuleCat.{v} B) [Module.Finite B N] (i : ℕ) :
    Module.Finite B (homWindow π N i).X₁ := sorry

/-- The middle term of a finite-free-resolution Hom window is finite when the target is finite. -/
@[stacks 0EH0 "finiteness of the middle Hom-window term"]
noncomputable instance finiteX₂ (N : ModuleCat.{v} B) [Module.Finite B N] (i : ℕ) :
    Module.Finite B (homWindow π N i).X₂ := sorry

/-- The right term of a finite-free-resolution Hom window is finite when the target is finite. -/
@[stacks 0EH0 "finiteness of the right Hom-window term"]
noncomputable instance finiteX₃ (N : ModuleCat.{v} B) [Module.Finite B N] (i : ℕ) :
    Module.Finite B (homWindow π N i).X₃ := sorry

/-- The finite-term package for a Hom window, assembled from the three canonical term
instances.  This is the preferred input to finite-window comparison APIs. -/
@[stacks 0EH0 "finite terms of a finite-resolution Hom window"]
theorem finiteTerms (N : ModuleCat.{v} B) [Module.Finite B N] (i : ℕ) :
    CategoryTheory.ShortComplex.IdealPower.FiniteTerms (homWindow π N i) := sorry

end HomWindow

/-- The canonical linear computation of Ext as homology of the resolution Hom window. -/
@[stacks 0EH0 "Ext as homology of a finite-free-resolution Hom window"]
noncomputable def extHomologyIso (N : ModuleCat.{v} B) (i : ℕ) :
    ModuleCat.of B (Ext M N i) ≅ (homWindow π N i).homology :=
  (ProjectiveResolution.extLinearEquivWindowHomology
    (P := ChainComplex.IsFreeResolution.toProjectiveResolution π)
    (Y := N) (n := i)).toModuleIso

/-- The ambient Ext quotient tower is the ambient-homology tower of the resolution window,
after restriction from `B` to `A`. -/
@[stacks 0EH0 "ambient Ext quotient tower as a Hom-window quotient tower"]
noncomputable def ambientTowerIso (I : Ideal A) (N : ModuleCat.{v} B) (i : ℕ) :
    quotientExtTower I M N i ≅
      CategoryTheory.ShortComplex.IdealPower.ambientTower (homWindow π N i)
          (mappedIdeal (A := A) (B := B) I) ⋙
        ModuleCat.restrictScalars (algebraMap A B) :=
  Functor.isoWhiskerRight
    (Ideal.PowerQuotient.positiveMapIso
      (mappedIdeal (A := A) (B := B) I) (extHomologyIso π N i))
    (ModuleCat.restrictScalars (algebraMap A B))

/-- The degree-`i` homology of the resolution Hom complex modulo the `n`th positive ideal
power, retained as a module over the quotient ring. -/
@[stacks 0EH0 "quotient-Hom resolution stage"]
abbrev stage (I : Ideal A) (N : ModuleCat.{v} B) (i n : ℕ) :
    ModuleCat.{v} (quotientRing (A := A) (B := B) I n) :=
  (HomologicalComplex.ModIdeal.complex (stageIdeal (A := A) (B := B) I n)
    (homComplex π N)).homology (i : ℤ)

/-- The scalar-restricted homology map induced by an arbitrary morphism of positive
ideal-power indices. -/
@[stacks 0EH0 "change of ideal on quotient-Hom resolution stages"]
def restrictedMap (I : Ideal A) (N : ModuleCat.{v} B) (i : ℕ)
    {X Y : ℕᵒᵖ} (f : X ⟶ Y) :
    (ModuleCat.restrictScalars
      (Ideal.Quotient.mk (stageIdeal (A := A) (B := B) I X.unop))).obj
        (stage (π := π) I N i X.unop) ⟶
      (ModuleCat.restrictScalars
        (Ideal.Quotient.mk (stageIdeal (A := A) (B := B) I Y.unop))).obj
          (stage (π := π) I N i Y.unop) :=
  (HomologicalComplex.ModIdeal.Homology.restrictedIso
      (stageIdeal (A := A) (B := B) I X.unop) (homComplex π N) (i : ℤ)).inv ≫
    HomologicalComplex.homologyMap
      (HomologicalComplex.ModIdeal.restrictedOfLE
        (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1))
        (homComplex π N)) (i : ℤ) ≫
    (HomologicalComplex.ModIdeal.Homology.restrictedIso
      (stageIdeal (A := A) (B := B) I Y.unop) (homComplex π N) (i : ℤ)).hom

/-- The quotient projection at the source of an index morphism factors through its ring map. -/
@[stacks 0EH0 "projection compatibility for quotient-Hom stages"]
theorem projectionCompatibility (I : Ideal A) {X Y : ℕᵒᵖ} (f : X ⟶ Y) :
    Ideal.Quotient.mk (stageIdeal (A := A) (B := B) I Y.unop) =
      ((quotientRingSystem (A := A) (B := B) I).map f).hom.comp
        (Ideal.Quotient.mk (stageIdeal (A := A) (B := B) I X.unop)) := sorry

/-- The quotient-ring-linear transition attached to an arbitrary morphism of positive
ideal-power indices. -/
@[stacks 0EH0 "varying-ring map on quotient-Hom resolution stages"]
def map (I : Ideal A) (N : ModuleCat.{v} B) (i : ℕ) {X Y : ℕᵒᵖ} (f : X ⟶ Y) :
    stage (π := π) I N i X.unop ⟶
      (ModuleCat.restrictScalars
        ((quotientRingSystem (A := A) (B := B) I).map f).hom).obj
          (stage (π := π) I N i Y.unop) :=
  ModuleCat.RestrictScalars.Surjective.preimage
    (Ideal.Quotient.mk (stageIdeal (A := A) (B := B) I X.unop))
    Ideal.Quotient.mk_surjective
    (restrictedMap (π := π) I N i f ≫
      (ModuleCat.restrictScalarsComp'
        (Ideal.Quotient.mk (stageIdeal (A := A) (B := B) I X.unop))
        ((quotientRingSystem (A := A) (B := B) I).map f).hom
        (Ideal.Quotient.mk (stageIdeal (A := A) (B := B) I Y.unop))
        (projectionCompatibility (A := A) (B := B) I f)).hom.app
          (stage (π := π) I N i Y.unop))

/-- The quotient-Hom transition attached to an identity index morphism is the canonical
restriction-along-identity comparison. -/
@[stacks 0EH0 "identity law for quotient-Hom resolution stages"]
theorem map_id (I : Ideal A) (N : ModuleCat.{v} B) (i : ℕ) (X : ℕᵒᵖ) :
    map (π := π) I N i (𝟙 X) =
      (ModuleCat.restrictScalarsId'
        ((quotientRingSystem (A := A) (B := B) I).map (𝟙 X)).hom
        (congrArg CommRingCat.Hom.hom
          ((quotientRingSystem (A := A) (B := B) I).map_id X))).inv.app
            (stage (π := π) I N i X.unop) := sorry

/-- Quotient-Hom transitions compose with the canonical comparison for iterated scalar
restriction. -/
@[stacks 0EH0 "composition law for quotient-Hom resolution stages"]
theorem map_comp (I : Ideal A) (N : ModuleCat.{v} B) (i : ℕ)
    {X Y Z : ℕᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (π := π) I N i (f ≫ g) =
      map (π := π) I N i f ≫
        (ModuleCat.restrictScalars
          ((quotientRingSystem (A := A) (B := B) I).map f).hom).map
            (map (π := π) I N i g) ≫
        (ModuleCat.restrictScalarsComp'
          ((quotientRingSystem (A := A) (B := B) I).map f).hom
          ((quotientRingSystem (A := A) (B := B) I).map g).hom
          ((quotientRingSystem (A := A) (B := B) I).map (f ≫ g)).hom
          (congrArg CommRingCat.Hom.hom
            ((quotientRingSystem (A := A) (B := B) I).map_comp f g))).inv.app
              (stage (π := π) I N i Z.unop) := sorry

/-- The presheaf of quotient-Hom homology modules over the positive quotient-ring system. -/
@[stacks 0EH0 "presheaf of quotient-Hom resolution stages"]
def presheaf (I : Ideal A) (N : ModuleCat.{v} B) (i : ℕ) :
    PresheafOfModules.{v}
      (bottomRingSheaf (quotientRingSystem (A := A) (B := B) I)).obj where
  obj X := stage (π := π) I N i X.unop
  map f := map (π := π) I N i f
  map_id X := map_id (π := π) I N i X
  map_comp f g := map_comp (π := π) I N i f g

/-- The strict varying-ring quotient-Hom tower determined by a chosen finite free resolution. -/
@[stacks 0EH0 "strict quotient-Hom tower from a finite free resolution"]
def tower (I : Ideal A) (N : ModuleCat.{v} B) (i : ℕ) :
    ModuleSystem.{u, v} (quotientRingSystem (A := A) (B := B) I) where
  val := presheaf (π := π) I N i
  isSheaf := Presheaf.isSheaf_bot _

/-- At stage `n`, the fixed-`B` quotient-window homology and the varying-ring resolution model
agree after both are restricted to `A`. -/
@[stacks 0EH0 "stage comparison between fixed- and varying-ring Hom-window models"]
noncomputable def stageOverAIso (I : Ideal A) (N : ModuleCat.{v} B) (i n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap A B)).obj
        (CategoryTheory.ShortComplex.IdealPower.stageHomology (homWindow π N i)
          (mappedIdeal (A := A) (B := B) I) n) ≅
      (reductionEvaluationOverA I n).obj (tower (π := π) I N i) :=
  (ModuleCat.restrictScalars (algebraMap A B)).mapIso
      (HomologicalComplex.ModIdeal.Homology.restrictedIso
        (mappedIdeal (A := A) (B := B) I ^ (n + 1)) (homComplex π N) (i : ℤ)) ≪≫
    (ModuleCat.restrictScalarsComp'
      (algebraMap A B)
      (Ideal.Quotient.mk (mappedIdeal (A := A) (B := B) I ^ (n + 1)))
      (quotientBaseMap (A := A) (B := B) I n)
      (quotientBaseMap_factor (A := A) (B := B) I n)).symm.app
        ((HomologicalComplex.ModIdeal.complex
          (mappedIdeal (A := A) (B := B) I ^ (n + 1))
          (homComplex π N)).homology (i : ℤ))

/-- The stage comparisons commute with every morphism of positive ideal-power indices. -/
@[stacks 0EH0 "naturality of the fixed- and varying-ring Hom-window comparison"]
theorem stageOverAIso_naturality (I : Ideal A) (N : ModuleCat.{v} B) (i : ℕ)
    {X Y : ℕᵒᵖ} (f : X ⟶ Y) :
    (CategoryTheory.ShortComplex.IdealPower.tower (homWindow π N i)
      (mappedIdeal (A := A) (B := B) I) ⋙
        ModuleCat.restrictScalars (algebraMap A B)).map f ≫
          (stageOverAIso π I N i Y.unop).hom =
      (stageOverAIso π I N i X.unop).hom ≫
        (reductionTowerOverA I (tower (π := π) I N i)).map f := sorry

/-- The fixed-ring quotient-window homology tower is canonically the restriction of the strict
varying-ring resolution tower. -/
@[stacks 0EH0 "fixed- and varying-ring Hom-window tower comparison"]
noncomputable def reducedTowerIso (I : Ideal A) (N : ModuleCat.{v} B) (i : ℕ) :
    CategoryTheory.ShortComplex.IdealPower.tower (homWindow π N i)
          (mappedIdeal (A := A) (B := B) I) ⋙
        ModuleCat.restrictScalars (algebraMap A B) ≅
      reductionTowerOverA I (tower (π := π) I N i) :=
  NatIso.ofComponents (fun X ↦ stageOverAIso π I N i X.unop)
    (stageOverAIso_naturality π I N i)

/-- The canonical tower morphism from quotients of ambient Ext to Ext computed after reduction.
Its middle factor is the generic `0EGU` homology comparison. -/
@[stacks 0EH0 "canonical tower comparison for Ext under ideal-power base change"]
noncomputable def towerComparison (I : Ideal A) (N : ModuleCat.{v} B) (i : ℕ) :
    quotientExtTower I M N i ⟶
      reductionTowerOverA I (tower (π := π) I N i) :=
  (ambientTowerIso π I N i).hom ≫
    Functor.whiskerRight
      (CategoryTheory.ShortComplex.IdealPower.comparison (homWindow π N i)
        (mappedIdeal (A := A) (B := B) I))
      (ModuleCat.restrictScalars (algebraMap A B)) ≫
    (reducedTowerIso π I N i).hom

/-- The component of the Ext base-change tower comparison is the ambient identification,
followed by the generic quotient-homology comparison and the varying-ring identification. -/
@[stacks 0EH0 "component of the Ext base-change tower comparison"]
theorem towerComparison_app (I : Ideal A) (N : ModuleCat.{v} B) (i n : ℕ) :
    (towerComparison π I N i).app (Opposite.op n) =
      (ambientTowerIso π I N i).hom.app (Opposite.op n) ≫
        (ModuleCat.restrictScalars (algebraMap A B)).map
          (CategoryTheory.ShortComplex.IdealPower.comparisonApp (homWindow π N i)
            (mappedIdeal (A := A) (B := B) I) n) ≫
        (reducedTowerIso π I N i).hom.app (Opposite.op n) := sorry

/-- The canonical map on inverse limits induced by the Ext base-change tower comparison. -/
@[stacks 0EH0 "canonical inverse-limit map for Ext under ideal-power base change"]
noncomputable def limitComparison (I : Ideal A) (N : ModuleCat.{v} B) (i : ℕ) :
    limit (quotientExtTower I M N i) ⟶
      limit (reductionTowerOverA I (tower (π := π) I N i)) :=
  Limits.lim.map (towerComparison π I N i)

/-- The concrete inverse-limit comparison attached to an explicit finite Hom-window
hypothesis.  This is the reusable core: finiteness of `N` is only one way to produce
`hfinite`. -/
@[stacks 0EH0 "inverse-limit Ext comparison from an explicit finite Hom window"]
noncomputable def limitIsoOfFiniteTerms [IsNoetherianRing B]
    (I : Ideal A) (N : ModuleCat.{v} B) (i : ℕ)
    (hfinite : CategoryTheory.ShortComplex.IdealPower.FiniteTerms (homWindow π N i)) :
    limit (quotientExtTower I M N i) ≅
      limit (reductionTowerOverA I (tower (π := π) I N i)) :=
  HasLimit.isoOfNatIso (ambientTowerIso π I N i) ≪≫
    (preservesLimitIso (ModuleCat.restrictScalars (algebraMap A B))
      (CategoryTheory.ShortComplex.IdealPower.ambientTower (homWindow π N i)
        (mappedIdeal (A := A) (B := B) I))).symm ≪≫
    (ModuleCat.restrictScalars (algebraMap A B)).mapIso
      (CategoryTheory.ShortComplex.IdealPower.FiniteTerms.limitIso
        (homWindow π N i) (mappedIdeal (A := A) (B := B) I) hfinite) ≪≫
    preservesLimitIso (ModuleCat.restrictScalars (algebraMap A B))
      (CategoryTheory.ShortComplex.IdealPower.tower (homWindow π N i)
        (mappedIdeal (A := A) (B := B) I)) ≪≫
    HasLimit.isoOfNatIso (reducedTowerIso π I N i)

/-- The forward map of `limitIsoOfFiniteTerms` is the canonical map induced by
`towerComparison`. -/
@[stacks 0EH0 "forward map of the explicit finite-window Ext comparison"]
theorem limitIsoOfFiniteTerms_hom [IsNoetherianRing B]
    (I : Ideal A) (N : ModuleCat.{v} B) (i : ℕ)
    (hfinite : CategoryTheory.ShortComplex.IdealPower.FiniteTerms (homWindow π N i)) :
    (limitIsoOfFiniteTerms π I N i hfinite).hom = limitComparison π I N i := sorry

/-- Over a Noetherian coefficient ring and for finite `N`, the canonical inverse-limit map is
an isomorphism.  This is the finite-three-term comparison of `0EGU` applied to the Hom window. -/
@[stacks 0EH0 "canonical inverse-limit comparison is an isomorphism"]
noncomputable instance limitComparison_isIso [IsNoetherianRing B]
    (I : Ideal A) (N : ModuleCat.{v} B) [Module.Finite B N] (i : ℕ) :
    IsIso (limitComparison π I N i) := sorry

/-- The canonical inverse-limit isomorphism induced by `towerComparison`. -/
@[stacks 0EH0 "canonical inverse-limit isomorphism for Ext base change"]
noncomputable def limitIso [IsNoetherianRing B]
    (I : Ideal A) (N : ModuleCat.{v} B) [Module.Finite B N] (i : ℕ) :
    limit (quotientExtTower I M N i) ≅
      limit (reductionTowerOverA I (tower (π := π) I N i)) :=
  limitIsoOfFiniteTerms π I N i
    (HomWindow.finiteTerms π N i)

/-- The finite-target specialization has the canonical tower comparison as its forward map. -/
@[stacks 0EH0 "forward map of the finite-target Ext limit isomorphism"]
theorem limitIso_hom [IsNoetherianRing B]
    (I : Ideal A) (N : ModuleCat.{v} B) [Module.Finite B N] (i : ℕ) :
    (limitIso π I N i).hom = limitComparison π I N i := sorry

/-- The chosen resolving complex after quotienting every term by the stage ideal. -/
@[stacks 0EH0 "stagewise quotient of a chosen resolution"]
abbrev reducedComplex (I : Ideal A) (n : ℕ) :
    ChainComplex (ModuleCat.{v} (quotientRing (A := A) (B := B) I n)) ℕ :=
  HomologicalComplex.ModIdeal.complex (stageIdeal (A := A) (B := B) I n) F

/-- The degree-zero quotient map induced by the chosen augmentation. -/
@[stacks 0EH0 "degree-zero map of the stagewise reduced augmentation"]
def reducedAugmentationZero (I : Ideal A) (n : ℕ) :
    (reducedComplex (F := F) I n).X 0 ⟶ reductionModule I M n :=
  ModuleCat.ofHom
    (HomologicalComplex.ModIdeal.mapLinear
      (stageIdeal (A := A) (B := B) I n) π 0)

/-- The degree-zero reduced augmentation annihilates the incoming differential. -/
@[stacks 0EH0 "chain condition for the stagewise reduced augmentation"]
theorem reducedAugmentationZero_condition (I : Ideal A) (n : ℕ) :
    (reducedComplex (F := F) I n).d 1 0 ≫ reducedAugmentationZero (π := π) I n = 0 := sorry

/-- The termwise quotient of the chosen augmentation. -/
@[stacks 0EH0 "augmentation of the stagewise reduced resolution"]
def reducedAugmentation (I : Ideal A) (n : ℕ) :
    reducedComplex (F := F) I n ⟶
      ChainComplex.moduleSingle (quotientRing (A := A) (B := B) I n)
        (reductionModule I M n) :=
  (ChainComplex.toSingle₀Equiv (reducedComplex (F := F) I n)
    (reductionModule I M n)).symm
      ⟨reducedAugmentationZero (π := π) I n,
        reducedAugmentationZero_condition (π := π) I n⟩

/-- Every term of the quotient of a finite free resolution is projective over the quotient
ring. -/
@[stacks 0EH0 "projectivity of a stagewise reduced resolution"]
theorem reducedComplex_projective (I : Ideal A) (n k : ℕ) :
    Projective ((reducedComplex (F := F) I n).X k) := sorry

/-- The reduced augmentation is a quasi-isomorphism under the flatness hypotheses of `0EH0`. -/
@[stacks 0EH0 "quasi-isomorphism for the stagewise reduced resolution"]
theorem reducedAugmentation_quasiIso
    (I : Ideal A) (n : ℕ)
    (hBflat : (algebraMap A B).Flat)
    (hMflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj M)) :
    QuasiIso (reducedAugmentation (π := π) I n) := sorry

/-- The projective resolution obtained by reducing the chosen finite free resolution at stage
`n`.  All data fields are canonical; only the named quasi-isomorphism theorem carries proof
debt. -/
@[stacks 0EH0 "stagewise reduced projective resolution"]
def reducedResolution (I : Ideal A) (n : ℕ)
    (hBflat : (algebraMap A B).Flat)
    (hMflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj M)) :
    ProjectiveResolution (reductionModule I M n) where
  complex := reducedComplex (F := F) I n
  projective k := reducedComplex_projective (F := F) I n k
  π := reducedAugmentation (π := π) I n
  quasiIso := reducedAugmentation_quasiIso (π := π) I n hBflat hMflat

/-- Each quotient-Hom stage computes Ext over the corresponding quotient ring.  The canonical
projective resolution used in this comparison is `reducedResolution`; the assertion itself is
kept proposition-valued so no arbitrary isomorphism is selected. -/
@[stacks 0EH0 "quotient-Hom stage computes reduced Ext"]
theorem stageIsomorphic
    (I : Ideal A) (N : ModuleCat.{v} B)
    (hBflat : (algebraMap A B).Flat)
    (hMflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj M))
    (i n : ℕ) :
    IsIsomorphic
      ((reductionEvaluation I n).obj (tower (π := π) I N i))
      (reductionExtStage I M N i n) := sorry

end ResolutionModel

/-! ### Comparison data from a chosen resolution -/

/-- A strict reduced Ext tower and its comparison morphism, indexed by one chosen finite free
resolution of `M`.  The tower, comparison, and inverse-limit isomorphism are retained as
concrete data; stage identification and the comparison's specification remain proposition-valued
laws. -/
@[stacks 0EH0 "resolution-indexed reduced Ext tower comparison"]
structure ResolutionComparison
    (I : Ideal A) (M N : ModuleCat.{v} B) [Small.{v} B] (i : ℕ)
    {F : ChainComplex (ModuleCat.{v} B) ℕ}
    (π : F ⟶ ChainComplex.moduleSingle B M) [ChainComplex.IsFiniteFreeResolution π] where
  /-- The strict varying-ring tower over the positive ideal-power quotients of `B`. -/
  reducedTower : ModuleSystem.{u, v} (quotientRingSystem (A := A) (B := B) I)
  /-- Every evaluated tower stage is isomorphic to the corresponding reduced Ext group.
This remains proposition-valued because the Hom complex of `reducedResolution` and the
quotient-Hom window are not definitionally the same complex; a concrete bridge must be supplied
by a separate comparison theorem. -/
  stageIsomorphic (n : ℕ) :
    IsIsomorphic ((reductionEvaluation I n).obj reducedTower) (reductionExtStage I M N i n)
  /-- The comparison from the ambient quotient tower to the restricted reduced tower. -/
  towerComparison : quotientExtTower I M N i ⟶ reductionTowerOverA I reducedTower
  /-- The concrete inverse-limit isomorphism carried by the comparison package. -/
  limitIso :
    limit (quotientExtTower I M N i) ≅ limit (reductionTowerOverA I reducedTower)
  /-- The forward map of `limitIso` is the map induced by `towerComparison`. -/
  limitIso_hom : limitIso.hom = Limits.lim.map towerComparison

namespace ResolutionComparison

variable [Small.{v} B]
variable {I : Ideal A} {M N : ModuleCat.{v} B} {i : ℕ}
variable {F : ChainComplex (ModuleCat.{v} B) ℕ}
variable {π : F ⟶ ChainComplex.moduleSingle B M} [ChainComplex.IsFiniteFreeResolution π]

/-- Stage `n` of the strict reduced tower attached to comparison data. -/
@[stacks 0EH0 "stage of a resolution-indexed reduced Ext tower"]
abbrev stage (C : ResolutionComparison I M N i π) (n : ℕ) :
    ModuleCat.{v} (quotientRing (A := A) (B := B) I n) :=
  (reductionEvaluation I n).obj C.reducedTower

/-- The varying-ring successor transition of a resolution-indexed reduced Ext tower. -/
@[stacks 0EH0 "transition of a resolution-indexed reduced Ext tower"]
abbrev step (C : ResolutionComparison I M N i π) (n : ℕ) :
    C.stage (n + 1) ⟶
      (ModuleCat.restrictScalars
        ((quotientRingSystem (A := A) (B := B) I).stepMap n).hom).obj (C.stage n) :=
  (evaluationStep (quotientRingSystem (A := A) (B := B) I) n).app C.reducedTower

/-- The fixed-`A` tower underlying resolution-indexed comparison data. -/
@[stacks 0EH0 "A-restricted tower of a resolution-indexed Ext comparison"]
noncomputable abbrev towerOverA (C : ResolutionComparison I M N i π) :
    SequentialInverseSystem (ModuleCat.{v} A) :=
  reductionTowerOverA I C.reducedTower

/-- Stage `n` of the fixed-`A` tower underlying resolution-indexed comparison data. -/
@[stacks 0EH0 "A-restricted stage of a resolution-indexed Ext comparison"]
abbrev stageOverA (C : ResolutionComparison I M N i π) (n : ℕ) : ModuleCat.{v} A :=
  (reductionEvaluationOverA I n).obj C.reducedTower

/-- The successor transition after restricting a resolution-indexed reduced tower to `A`. -/
@[stacks 0EH0 "A-restricted transition of a resolution-indexed Ext comparison"]
noncomputable abbrev stepOverA (C : ResolutionComparison I M N i π) (n : ℕ) :
    C.stageOverA (n + 1) ⟶ C.stageOverA n :=
  (restrictEvaluationStep (quotientRingSystem (A := A) (B := B) I)
    (quotientCone (A := A) (B := B) I) n).app C.reducedTower

/-- The canonical inverse-limit map carried by resolution-indexed comparison data. -/
@[stacks 0EH0 "inverse-limit map of resolution-indexed comparison data"]
noncomputable abbrev limitComparison (C : ResolutionComparison I M N i π) :
    limit (quotientExtTower I M N i) ⟶ limit C.towerOverA :=
  Limits.lim.map C.towerComparison

/-- The proposition-valued inverse-limit statement carried by resolution-indexed comparison data.
The concrete isomorphism itself is the `limitIso` field. -/
@[stacks 0EH0 "inverse-limit isomorphism of resolution-indexed comparison data"]
theorem limitComparisonIsIso (C : ResolutionComparison I M N i π) :
    IsIso C.limitComparison := sorry

/-- Construct comparison data from a chosen finite free resolution and an explicit finite
Hom-window hypothesis.  This is the general constructor; finiteness of `N` is only a convenient
way to obtain the final argument through `HomWindow.finiteTerms`. -/
@[stacks 0EH0 "comparison data from an explicit finite Hom window"]
noncomputable def ofFiniteTerms
    [IsNoetherianRing B] (I : Ideal A) (N : ModuleCat.{v} B)
    (hBflat : (algebraMap A B).Flat)
    (hMflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj M))
    (i : ℕ) {F : ChainComplex (ModuleCat.{v} B) ℕ}
    (π : F ⟶ ChainComplex.moduleSingle B M) [ChainComplex.IsFiniteFreeResolution π]
    (hfinite : CategoryTheory.ShortComplex.IdealPower.FiniteTerms (ResolutionModel.homWindow π N i)) :
    ResolutionComparison I M N i π where
  reducedTower := ResolutionModel.tower (π := π) I N i
  stageIsomorphic n := ResolutionModel.stageIsomorphic π I N hBflat hMflat i n
  towerComparison := ResolutionModel.towerComparison π I N i
  limitIso := ResolutionModel.limitIsoOfFiniteTerms π I N i hfinite
  limitIso_hom := ResolutionModel.limitIsoOfFiniteTerms_hom π I N i hfinite

/-- Construct the comparison package from a chosen finite free resolution.  The quotient-Hom
tower and its inverse-limit isomorphism are supplied by the canonical `ResolutionModel` owners. -/
@[stacks 0EH0 "comparison data from a chosen finite free resolution"]
noncomputable def ofResolution
    [IsNoetherianRing B] (I : Ideal A) (N : ModuleCat.{v} B) [Module.Finite B N]
    (hBflat : (algebraMap A B).Flat)
    (hMflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj M))
    (i : ℕ) {F : ChainComplex (ModuleCat.{v} B) ℕ}
    (π : F ⟶ ChainComplex.moduleSingle B M) [ChainComplex.IsFiniteFreeResolution π] :
    ResolutionComparison I M N i π :=
  ofFiniteTerms I N hBflat hMflat i π (ResolutionModel.HomWindow.finiteTerms π N i)

end ResolutionComparison

/-- Lemma 15.101.11 (0EH0): under flat base change, the ambient Ext quotient tower admits a
strict reduced-stage representative and a comparison whose induced inverse-limit map is the
forward map of a concrete isomorphism.  The well-typed reading uses `B`-modules; finiteness of
both modules supplies the finite free resolution and the finite Hom-window terms used by
`0EGU`. -/
@[stacks 0EH0 "limit comparison for Ext under flat ideal-power base change"]
theorem existsReductionTowerComparison
    [IsNoetherianRing A] [IsNoetherianRing B] [Small.{v} B]
    (I : Ideal A) (M N : ModuleCat.{v} B)
    [Module.Finite B M] [Module.Finite B N]
    (hBflat : (algebraMap A B).Flat)
    (hMflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj M))
    (i : ℕ) :
    ∃ T : ModuleSystem.{u, v} (quotientRingSystem (A := A) (B := B) I),
      ∃ α : quotientExtTower I M N i ⟶ reductionTowerOverA I T,
        ∃ e : limit (quotientExtTower I M N i) ≅ limit (reductionTowerOverA I T),
          (∀ n : ℕ,
            IsIsomorphic ((reductionEvaluation I n).obj T) (reductionExtStage I M N i n)) ∧
          e.hom = Limits.lim.map α := sorry

end IadicFiniteModuleSystem.Ext.BaseChange

end
