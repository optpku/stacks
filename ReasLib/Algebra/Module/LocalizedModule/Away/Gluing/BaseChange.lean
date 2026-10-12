/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.BaseChange
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Hom
public import ReasLib.Algebra.Module.LocalizedModule.Away.Iterated.Equiv
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base Change of Principal-Open Module Gluing Data

This leaf extends every local module along the base-changed principal-open
map and transports its pairwise overlap isomorphisms to the literal target
products `φ (f i) * φ (f j)`.

@stack 00EK
@stack 05EQ
-/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u v w

noncomputable section

namespace LocalizedModule.Away

variable {R S : Type u} [CommRing R] [CommRing S]
variable {ι : Type w} {f : ι → R}

namespace PreGluing

variable (data : PreGluing f)

/-- Extend the underlying `R`-module of the `i`-th local piece along a ring
map `φ : R →+* S`. -/
@[stacks 05EQ "principal-open pregluing underlying base change"]
noncomputable abbrev baseChangeUnderlying (φ : R →+* S) (i : ι) :
    ModuleCat.{max u v} S :=
  (ModuleCat.extendScalars φ).obj (ModuleCat.of R (data.localModule i))

/-- The `i`-th local piece after base change, localized on the target
principal open `D(φ (f i))`. -/
@[stacks 00EK "principal-open pregluing base-changed local piece",
  stacks 05EQ "principal-open pregluing base-changed local piece"]
noncomputable def baseChangeLocalModule (φ : R →+* S) (i : ι) :
    ModuleCat.{max u v} (Localization.Away (φ (f i))) :=
  ModuleCat.of (Localization.Away (φ (f i)))
    (LocalizedModule.Away (φ (f i)) (data.baseChangeUnderlying φ i))

/-- The `S`-module obtained by restricting scalars on the bundled
base-changed local piece.  Naming this view isolates the scalar-action choice
made by `ModuleCat.Algebra`. -/
@[stacks 05EQ "base-changed local piece restricted scalar view"]
noncomputable abbrev baseChangeLocalModuleRestrict (φ : R →+* S) (i : ι) :
    ModuleCat.{max u v} S :=
  ModuleCat.of S (data.baseChangeLocalModule φ i)

/-- The direct canonical `S`-module structure on the localized carrier of a
base-changed local piece. -/
@[stacks 05EQ "base-changed local piece direct scalar view"]
noncomputable abbrev baseChangeLocalModuleDirect (φ : R →+* S) (i : ι) :
    ModuleCat.{max u v} S :=
  ModuleCat.of S
    (LocalizedModule.Away (φ (f i)) (data.baseChangeUnderlying φ i))

/-- The restricted and direct `S`-module structures on a base-changed local
piece define the same bundled module. -/
@[stacks 05EQ "base-changed local piece scalar-action compatibility"]
theorem baseChangeLocalModuleRestrict_eq_direct (φ : R →+* S) (i : ι) :
    data.baseChangeLocalModuleRestrict φ i =
      data.baseChangeLocalModuleDirect φ i := sorry

/-- The canonical `S`-linear equivalence between the restricted and direct
scalar views of a base-changed local piece. -/
@[stacks 05EQ "base-changed local piece scalar comparison"]
noncomputable def baseChangeLocalModuleEquiv (φ : R →+* S) (i : ι) :
    data.baseChangeLocalModuleRestrict φ i ≃ₗ[S]
      data.baseChangeLocalModuleDirect φ i :=
  (eqToIso (data.baseChangeLocalModuleRestrict_eq_direct φ i)).toLinearEquiv

/-- Localizing an already localized local piece once more at its defining
denominator canonically recovers that local piece. -/
@[stacks 00EK "principal-open local-piece idempotent localization"]
noncomputable def localModuleIdIso (i : ι) :
    ModuleCat.of (Localization.Away (f i))
        (LocalizedModule.Away (f i) (data.localModule i)) ≅
      data.localModule i :=
  ((LocalizedModule.Away.idLinearEquiv (f i)).extendScalarsOfIsLocalization
    (Submonoid.powers (f i)) (Localization.Away (f i))).toModuleIso

/-- The base-changed local piece is canonically scalar extension of the
original local piece along the induced map of principal localization rings. -/
@[stacks 00EK "principal-open pregluing local-piece base-change comparison",
  stacks 05EQ "principal-open pregluing local-piece base-change comparison"]
noncomputable def baseChangeLocalModuleIso (φ : R →+* S) (i : ι) :
    data.baseChangeLocalModule φ i ≅
      (ModuleCat.extendScalars (Localization.awayMap φ (f i))).obj
        (data.localModule i) :=
  LocalizedModule.Away.baseChangeIso φ (f i)
      (ModuleCat.of R (data.localModule i)) ≪≫
    (ModuleCat.extendScalars
      (Localization.awayMap φ (f i))).mapIso (data.localModuleIdIso i)

/-- The canonical map from an original local piece to its base-changed local
piece, viewed after restriction along `Localization.awayMap φ (f i)`.
It is the scalar-extension unit followed by the inverse local comparison. -/
@[stacks 00EK "principal-open local-piece base-change unit",
  stacks 05EQ "principal-open local-piece base-change unit"]
noncomputable def baseChangeUnit (φ : R →+* S) (i : ι) :
    data.localModule i ⟶
      (ModuleCat.restrictScalars
        (Localization.awayMap φ (f i))).obj
          (data.baseChangeLocalModule φ i) :=
  ModuleCat.ExtendRestrictScalarsAdj.Unit.map
      (Localization.awayMap φ (f i)) ≫
    (ModuleCat.restrictScalars
      (Localization.awayMap φ (f i))).map
        (data.baseChangeLocalModuleIso φ i).inv

/-- Composing `baseChangeUnit` with the forward local comparison recovers
the ordinary scalar-extension unit.  This characterizes the chosen map
without exposing a tensor-carrier formula. -/
@[stacks 05EQ "principal-open local-piece base-change unit specification"]
theorem baseChangeUnit_comp_iso_hom (φ : R →+* S) (i : ι) :
    data.baseChangeUnit φ i ≫
        (ModuleCat.restrictScalars
          (Localization.awayMap φ (f i))).map
            (data.baseChangeLocalModuleIso φ i).hom =
      ModuleCat.ExtendRestrictScalarsAdj.Unit.map
        (Localization.awayMap φ (f i)) := sorry

/-- The overlap module of a base-changed local piece, with the restricted
`S`-module action fixed to the canonical `ModuleCat.Algebra` action. -/
@[stacks 00EK "principal-open base-changed overlap module",
  stacks 05EQ "principal-open base-changed overlap module"]
noncomputable def baseChangeOverlapModule (φ : R →+* S) (i : ι) (d : S) :
    ModuleCat.{max u v} (Localization.Away d) :=
  ModuleCat.of (Localization.Away d)
    (LocalizedModule.Away d (data.baseChangeLocalModule φ i))

/-- Normalize the base-changed `i`-side overlap to scalar extension of the
original `i`-side product localization. -/
@[stacks 00EK "principal-open pregluing left overlap base change",
  stacks 05EQ "principal-open pregluing left overlap base change"]
noncomputable def baseChangeLeftOverlapIso (φ : R →+* S) (i j : ι) :
    data.baseChangeOverlapModule φ i (φ (f i) * φ (f j)) ≅
      (ModuleCat.extendScalars
          (Localization.Away.productMap φ (f i) (f j))).obj
        (ModuleCat.of (Localization.Away (f i * f j))
          (LocalizedModule.Away (f i * f j) (data.localModule i))) :=
  (LocalizedModule.mapEquiv
      (Submonoid.powers (φ (f i) * φ (f j)))
      (data.baseChangeLocalModuleEquiv φ i)).toModuleIso ≪≫
    (LocalizedModule.Away.Iterated.leftOverlapEquiv
      (φ (f i)) (φ (f j)) (data.baseChangeUnderlying φ i)).toModuleIso ≪≫
    LocalizedModule.Away.productBaseChangeIso φ (f i) (f j)
      (ModuleCat.of R (data.localModule i))

/-- Normalize the base-changed `j`-side overlap to scalar extension of the
original `j`-side product localization, with the same ordered target product
as the `i`-side. -/
@[stacks 00EK "principal-open pregluing right overlap base change",
  stacks 05EQ "principal-open pregluing right overlap base change"]
noncomputable def baseChangeRightOverlapIso (φ : R →+* S) (i j : ι) :
    data.baseChangeOverlapModule φ j (φ (f i) * φ (f j)) ≅
      (ModuleCat.extendScalars
          (Localization.Away.productMap φ (f i) (f j))).obj
        (ModuleCat.of (Localization.Away (f i * f j))
          (LocalizedModule.Away (f i * f j) (data.localModule j))) :=
  (LocalizedModule.mapEquiv
      (Submonoid.powers (φ (f i) * φ (f j)))
      (data.baseChangeLocalModuleEquiv φ j)).toModuleIso ≪≫
    (LocalizedModule.Away.Iterated.rightOverlapEquiv
      (φ (f i)) (φ (f j)) (data.baseChangeUnderlying φ j)).toModuleIso ≪≫
    LocalizedModule.Away.productBaseChangeIso φ (f i) (f j)
      (ModuleCat.of R (data.localModule j))

/-- The pairwise overlap isomorphism after base change: normalize the left
piece, extend the original overlap isomorphism, and undo the right
normalization. -/
@[stacks 00EK "principal-open pregluing base-changed overlap isomorphism",
  stacks 05EQ "principal-open pregluing base-changed overlap isomorphism"]
noncomputable def baseChangeOverlapIso (φ : R →+* S) (i j : ι) :
    data.baseChangeOverlapModule φ i (φ (f i) * φ (f j)) ≅
      data.baseChangeOverlapModule φ j (φ (f i) * φ (f j)) :=
  data.baseChangeLeftOverlapIso φ i j ≪≫
    (ModuleCat.extendScalars
      (Localization.Away.productMap φ (f i) (f j))).mapIso
        (data.overlapIso i j) ≪≫
    (data.baseChangeRightOverlapIso φ i j).symm

/-- Base change of principal-open pregluing data.  This declaration contains
all local modules and pairwise overlap isomorphisms but no cocycle proof. -/
@[stacks 00EK "principal-open module pregluing base change",
  stacks 05EQ "principal-open module pregluing base change"]
noncomputable def baseChange (φ : R →+* S) :
    PreGluing (fun i ↦ φ (f i)) where
  localModule i := data.baseChangeLocalModule φ i
  overlapIso i j := data.baseChangeOverlapIso φ i j

/-- The local-module projection of a base-changed pregluing datum is the
canonical base-changed local piece. -/
@[simp, stacks 05EQ "principal-open pregluing base change local piece projection"]
theorem baseChange_localModule (φ : R →+* S) (i : ι) :
    (data.baseChange φ).localModule i = data.baseChangeLocalModule φ i := sorry

/-- The overlap projection of a base-changed pregluing datum is the canonical
three-step transported overlap isomorphism. -/
@[simp, stacks 05EQ "principal-open pregluing base change overlap projection"]
theorem baseChange_overlapIso (φ : R →+* S) (i j : ι) :
    (data.baseChange φ).overlapIso i j = data.baseChangeOverlapIso φ i j := sorry

end PreGluing

namespace Gluing

variable (glue : Gluing f)

/-- Base change preserves the triple-overlap cocycle condition. -/
@[stacks 00EK "principal-open gluing base-change cocycle",
  stacks 05EQ "principal-open gluing base-change cocycle"]
theorem baseChange_cocycle (φ : R →+* S) :
    PreGluing.CocycleCondition (glue.toPreGluing.baseChange φ) := sorry

/-- Base change of a principal-open module gluing datum.  The concrete local
pieces and overlap isomorphisms are owned by `PreGluing.baseChange`; only the
cocycle certificate is added here. -/
@[stacks 00EK "principal-open module gluing base change",
  stacks 05EQ "principal-open module gluing base change"]
noncomputable def baseChange (φ : R →+* S) :
    Gluing (fun i ↦ φ (f i)) where
  toPreGluing := glue.toPreGluing.baseChange φ
  cocycle := glue.baseChange_cocycle φ

/-- Forgetting the cocycle from a base-changed gluing datum recovers the
base-changed underlying pregluing datum. -/
@[simp, stacks 05EQ "principal-open gluing base change underlying pregluing"]
theorem baseChange_toPreGluing (φ : R →+* S) :
    (glue.baseChange φ).toPreGluing = glue.toPreGluing.baseChange φ := sorry

/-- Extend the underlying base-ring map of the `i`-th local component of a
gluing morphism along `φ`. -/
@[stacks 00EK "principal-open gluing morphism underlying base change",
  stacks 05EQ "principal-open gluing morphism underlying base change"]
noncomputable def baseChangeMapUnderlying {X Y : Gluing f}
    (φ : R →+* S) (ψ : X ⟶ Y) (i : ι) :
    X.toPreGluing.baseChangeUnderlying φ i ⟶
      Y.toPreGluing.baseChangeUnderlying φ i :=
  (ModuleCat.extendScalars φ).map
    (ModuleCat.ofHom ((ψ.hom i).hom.restrictScalars R))

/-- Localize the extended `i`-th component of a gluing morphism at the
base-changed denominator `φ (f i)`. -/
@[stacks 00EK "principal-open gluing morphism local base change",
  stacks 05EQ "principal-open gluing morphism local base change"]
noncomputable def baseChangeMapLocal {X Y : Gluing f}
    (φ : R →+* S) (ψ : X ⟶ Y) (i : ι) :
    (X.baseChange φ).localModule i ⟶ (Y.baseChange φ).localModule i :=
  ModuleCat.ofHom <| LocalizedModule.map
    (Submonoid.powers (φ (f i))) (baseChangeMapUnderlying φ ψ i).hom

/-- The base-changed local components of a gluing morphism commute with the
transported pairwise overlap isomorphisms. -/
@[stacks 00EK "principal-open gluing morphism base-change naturality",
  stacks 05EQ "principal-open gluing morphism base-change naturality"]
theorem baseChangeMap_comm {X Y : Gluing f}
    (φ : R →+* S) (ψ : X ⟶ Y) :
    ∀ i j : ι,
      CommSq
        (ModuleCat.ofHom <| LocalizedModule.map
          (Submonoid.powers (φ (f i) * φ (f j)))
          ((baseChangeMapLocal φ ψ i).hom.restrictScalars S))
        ((X.baseChange φ).overlapIso i j).hom
        ((Y.baseChange φ).overlapIso i j).hom
        (ModuleCat.ofHom <| LocalizedModule.map
          (Submonoid.powers (φ (f i) * φ (f j)))
          ((baseChangeMapLocal φ ψ j).hom.restrictScalars S)) := sorry

/-- Base change of a morphism between principal-open gluing data. -/
@[stacks 00EK "principal-open gluing morphism base change",
  stacks 05EQ "principal-open gluing morphism base change"]
noncomputable def baseChangeMap {X Y : Gluing f}
    (φ : R →+* S) (ψ : X ⟶ Y) :
    X.baseChange φ ⟶ Y.baseChange φ where
  hom i := baseChangeMapLocal φ ψ i
  comm := baseChangeMap_comm φ ψ

/-- The local base-change units commute with every morphism of gluing data. -/
@[stacks 00EK "principal-open local base-change unit naturality",
  stacks 05EQ "principal-open local base-change unit naturality"]
theorem baseChangeUnit_naturality {X Y : Gluing f}
    (φ : R →+* S) (ψ : X ⟶ Y) (i : ι) :
    ψ.hom i ≫ Y.toPreGluing.baseChangeUnit φ i =
      X.toPreGluing.baseChangeUnit φ i ≫
        (ModuleCat.restrictScalars
          (Localization.awayMap φ (f i))).map
            ((baseChangeMap φ ψ).hom i) := sorry

/-- The local component of a base-changed gluing morphism is the localization
of its extended underlying component. -/
@[simp, stacks 05EQ "principal-open gluing morphism base-change component"]
theorem baseChangeMap_hom {X Y : Gluing f}
    (φ : R →+* S) (ψ : X ⟶ Y) (i : ι) :
    (baseChangeMap φ ψ).hom i = baseChangeMapLocal φ ψ i := sorry

/-- Base change sends the identity gluing morphism to the identity. -/
@[stacks 05EQ "principal-open gluing base-change identity"]
theorem baseChangeMap_id (φ : R →+* S) (X : Gluing f) :
    baseChangeMap φ (𝟙 X) = 𝟙 (X.baseChange φ) := sorry

/-- Base change sends a composite of gluing morphisms to the composite of
their base changes. -/
@[stacks 05EQ "principal-open gluing base-change composition"]
theorem baseChangeMap_comp (φ : R →+* S) {X Y Z : Gluing f}
    (ψ : X ⟶ Y) (χ : Y ⟶ Z) :
    baseChangeMap φ (ψ ≫ χ) = baseChangeMap φ ψ ≫ baseChangeMap φ χ := sorry

/-- Base change of principal-open module gluing data, packaged as a functor.
The target family is the literal pointwise image `fun i ↦ φ (f i)`. -/
@[stacks 00EK "principal-open module gluing base-change functor",
  stacks 05EQ "principal-open module gluing base-change functor"]
noncomputable def baseChangeFunctor (φ : R →+* S) :
    Gluing f ⥤ Gluing (fun i ↦ φ (f i)) where
  obj X := X.baseChange φ
  map ψ := baseChangeMap φ ψ
  map_id := baseChangeMap_id φ
  map_comp := baseChangeMap_comp φ

end Gluing

end LocalizedModule.Away
