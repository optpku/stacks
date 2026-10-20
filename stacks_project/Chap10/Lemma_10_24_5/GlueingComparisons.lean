module
public import stacks_project.Chap10.Lemma_10_24_1
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict
public import ReasLib.Algebra.Module.LocalizedModule.Away.Iterated.Equiv
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Hom
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Local
public import ReasLib.Algebra.Module.LocalizedModule.Pi

/-!
@stack 00EK
@stack 00EQ
# Source view of principal-open module gluing

The concrete `AwayModuleGlueing` presentation remains source-facing.  Its
`toGluing` view and local-recovery bridge below point to the generalized
`LocalizedModule.Away.Gluing` owner without moving chapter-specific kernel
comparisons or triple-product normal forms into the shared library.

The historical names `awayLocalizationCompatibilityMap`, `awayEqLinearEquiv`,
`awayMulLinearEquiv`, and `iteratedLocalizedModuleMkLinearMap` are owned by
Lemma 10.24.1 and imported here.  This preserves the downstream ABI without
creating a second set of root declarations when the chapter aggregate imports
both source items.

Likewise, the historical name `awayLocalizeLinearEquiv` is now a direct alias
of `LocalizedModule.Away.mapEquiv`; only its source-facing generator formulas
remain as compatibility lemmas.

The remaining source compatibility names do not introduce parallel data:
`localModuleAwayEquiv` is the canonical
`LocalizedModule.Away.idLinearEquiv` for the local piece.  The middle and
target product comparisons likewise use the canonical finite-product owner
`LocalizedModule.piLinearEquiv` before applying the source overlap transports.

The named law lemmas used to assemble public structures also remain public:
Lean does not allow exported data to depend on private declarations, and the
statement stage requires proof obligations to be separate `:= sorry`
declarations.  They are construction laws, not competing mathematical owners.
-/

@[expose] public section

open CategoryTheory LinearMap LocalizedModule IsLocalizedModule

universe u v w

noncomputable section

section LocalizationMap

variable {R : Type u} [CommSemiring R]

local notation "Away" => LocalizedModule.Away

/-- Legacy source-facing name for the canonical equivalence obtained by
localizing an `R`-linear equivalence away from `a`. -/
noncomputable abbrev awayLocalizeLinearEquiv
    {M : Type v} {N : Type w} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (a : R) (e : M ≃ₗ[R] N) :
    Away a M ≃ₗ[R] Away a N :=
  LocalizedModule.Away.mapEquiv a e

/-- Localizing a linear equivalence away from `a` applies it to the numerator
of a localized element with an arbitrary denominator. -/
@[simp]
theorem awayLocalizeLinearEquiv_apply_mk
    {M : Type v} {N : Type w} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (a : R) (e : M ≃ₗ[R] N) (x : M) (s : Submonoid.powers a) :
    awayLocalizeLinearEquiv a e (LocalizedModule.mk x s) =
      LocalizedModule.mk (e x) s := sorry

/-- The inverse localized equivalence applies the inverse original
equivalence to the numerator with an arbitrary denominator. -/
@[simp]
theorem awayLocalizeLinearEquiv_symm_apply_mk
    {M : Type v} {N : Type w} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (a : R) (e : M ≃ₗ[R] N) (x : N) (s : Submonoid.powers a) :
    (awayLocalizeLinearEquiv a e).symm (LocalizedModule.mk x s) =
      LocalizedModule.mk (e.symm x) s := sorry

/-- Localizing a linear equivalence away from `a` sends a canonical generator
to the canonical generator of its image. -/
@[simp]
theorem awayLocalizeLinearEquiv_apply_mk_one
    {M : Type v} {N : Type w} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (a : R) (e : M ≃ₗ[R] N) (x : M) :
    awayLocalizeLinearEquiv a e (LocalizedModule.mk x 1) =
      LocalizedModule.mk (e x) 1 := sorry

/-- The inverse localized equivalence sends a canonical generator to the
canonical generator of its inverse image. -/
@[simp]
theorem awayLocalizeLinearEquiv_symm_apply_mk_one
    {M : Type v} {N : Type w} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (a : R) (e : M ≃ₗ[R] N) (x : N) :
    (awayLocalizeLinearEquiv a e).symm (LocalizedModule.mk x 1) =
      LocalizedModule.mk (e.symm x) 1 := sorry

#check @LocalizedModule.Away.map
#check @LocalizedModule.Away.mapEquiv
#print axioms LocalizedModule.Away.mapEquiv
#print axioms awayLocalizeLinearEquiv

end LocalizationMap

section

variable {R : Type u} [CommRing R]
variable {n : ℕ}

local notation "Away" => LocalizedModule.Away

#check @awayLocalizationCompatibilityMap
#check @AwayLocalization.compatibilityMap_eq
#check @iteratedLocalizedModuleMkLinearMap
#check @iteratedLocalizedModule_isLocalizedModule_sup
#check @mkLinearMap_isLocalizedModule_sup_away_mul
#check @mkLinearMap_isLocalizedModule_sup_away_mul'
#check @awayEqLinearEquiv
#check @awayEqLinearEquiv_apply_mk_one
#check @awayMulLinearEquiv
#print axioms awayLocalizationCompatibilityMap
#print axioms iteratedLocalizedModuleMkLinearMap
#print axioms awayEqLinearEquiv
#print axioms awayMulLinearEquiv

/-- Transport from the `i`-piece to the `j`-piece on the common triple overlap. -/
noncomputable abbrev awayModuleGlueingTripleOverlapHom12
    (f : Fin n → R) (localModule : ∀ i, ModuleCat.{max u v} (Localization.Away (f i)))
    (overlapIso : ∀ i j,
      ModuleCat.of (Localization.Away (f i * f j))
          (Away (f i * f j) (localModule i)) ≅
        ModuleCat.of (Localization.Away (f i * f j))
          (Away (f i * f j) (localModule j)))
    (i j k : Fin n) :
    Away (f i * f j * f k) (localModule i) ≃ₗ[R]
      Away (f i * f j * f k) (localModule j) :=
  (LocalizedModule.Away.Iterated.baseMulEquiv
      (f i * f j) (f k) (localModule i)).symm.trans
    ((LocalizedModule.Away.mapEquiv
        (f k) ((overlapIso i j).toLinearEquiv.restrictScalars R)).trans
      (LocalizedModule.Away.Iterated.baseMulEquiv
        (f i * f j) (f k) (localModule j)))

/-- Transport from the `j`-piece to the `k`-piece on the common triple overlap. -/
noncomputable abbrev awayModuleGlueingTripleOverlapHom23
    (f : Fin n → R) (localModule : ∀ i, ModuleCat.{max u v} (Localization.Away (f i)))
    (overlapIso : ∀ i j,
      ModuleCat.of (Localization.Away (f i * f j))
          (Away (f i * f j) (localModule i)) ≅
        ModuleCat.of (Localization.Away (f i * f j))
          (Away (f i * f j) (localModule j)))
    (i j k : Fin n) :
    Away (f i * f j * f k) (localModule j) ≃ₗ[R] Away (f i * f j * f k) (localModule k) :=
  let left :
      Away (f i * f j * f k) (localModule j) ≃ₗ[R] Away (f j * f k * f i) (localModule j) :=
    LocalizedModule.Away.Iterated.denominatorEquiv
      (localModule j) (mul_rotate (f i) (f j) (f k))
  let center :
      Away (f j * f k * f i) (localModule j) ≃ₗ[R] Away (f j * f k * f i) (localModule k) :=
    (LocalizedModule.Away.Iterated.baseMulEquiv
        (f j * f k) (f i) (localModule j)).symm.trans
      ((LocalizedModule.Away.mapEquiv
          (f i) ((overlapIso j k).toLinearEquiv.restrictScalars R)).trans
        (LocalizedModule.Away.Iterated.baseMulEquiv
          (f j * f k) (f i) (localModule k)))
  let right :
      Away (f j * f k * f i) (localModule k) ≃ₗ[R] Away (f i * f j * f k) (localModule k) :=
    LocalizedModule.Away.Iterated.denominatorEquiv
      (localModule k) (mul_rotate (f i) (f j) (f k)).symm
  left.trans (center.trans right)

/-- Direct transport from the `i`-piece to the `k`-piece on the common triple overlap. -/
noncomputable abbrev awayModuleGlueingTripleOverlapHom13
    (f : Fin n → R) (localModule : ∀ i, ModuleCat.{max u v} (Localization.Away (f i)))
    (overlapIso : ∀ i j,
      ModuleCat.of (Localization.Away (f i * f j))
          (Away (f i * f j) (localModule i)) ≅
        ModuleCat.of (Localization.Away (f i * f j))
          (Away (f i * f j) (localModule j)))
    (i j k : Fin n) :
    Away (f i * f j * f k) (localModule i) ≃ₗ[R] Away (f i * f j * f k) (localModule k) :=
  let left :
      Away (f i * f j * f k) (localModule i) ≃ₗ[R] Away (f i * f k * f j) (localModule i) :=
    LocalizedModule.Away.Iterated.denominatorEquiv
      (localModule i) (mul_right_comm (f i) (f j) (f k))
  let center :
      Away (f i * f k * f j) (localModule i) ≃ₗ[R] Away (f i * f k * f j) (localModule k) :=
    (LocalizedModule.Away.Iterated.baseMulEquiv
        (f i * f k) (f j) (localModule i)).symm.trans
      ((LocalizedModule.Away.mapEquiv
          (f j) ((overlapIso i k).toLinearEquiv.restrictScalars R)).trans
        (LocalizedModule.Away.Iterated.baseMulEquiv
          (f i * f k) (f j) (localModule k)))
  let right :
      Away (f i * f k * f j) (localModule k) ≃ₗ[R] Away (f i * f j * f k) (localModule k) :=
    LocalizedModule.Away.Iterated.denominatorEquiv
      (localModule k) (mul_right_comm (f i) (f j) (f k)).symm
  left.trans (center.trans right)

/-- The cocycle condition for pairwise overlap isomorphisms in a finite
principal-open module gluing datum. -/
@[stacks 00EK "source finite principal-open gluing cocycle"]
def AwayModuleGlueingCocycleCondition
    (f : Fin n → R) (localModule : ∀ i, ModuleCat.{max u v} (Localization.Away (f i)))
    (overlapIso : ∀ i j,
      ModuleCat.of (Localization.Away (f i * f j))
          (Away (f i * f j) (localModule i)) ≅
        ModuleCat.of (Localization.Away (f i * f j))
          (Away (f i * f j) (localModule j))) :
    Prop :=
  ∀ i j k : Fin n,
    (awayModuleGlueingTripleOverlapHom12 f localModule overlapIso i j k).trans
      (awayModuleGlueingTripleOverlapHom23 f localModule overlapIso i j k) =
    awayModuleGlueingTripleOverlapHom13 f localModule overlapIso i j k

/-- A finite module gluing on the standard cover defined by `f`. The primitive local pieces are
actual `R_(fᵢ)`-modules, and the overlap data are actual `R_(fᵢfⱼ)`-linear isomorphisms. -/
@[stacks 00EK "source finite principal-open module gluing datum"]
structure AwayModuleGlueing (f : Fin n → R) where
  /-- The module carried by the principal open `D(f i)`. -/
  localModule : ∀ i, ModuleCat.{max u v} (Localization.Away (f i))
  /-- The identification of the two local modules over `D(f i * f j)`. -/
  overlapIso : ∀ i j,
    ModuleCat.of (Localization.Away (f i * f j))
        (Away (f i * f j) (localModule i)) ≅
      ModuleCat.of (Localization.Away (f i * f j))
        (Away (f i * f j) (localModule j))
  /-- Compatibility of the pairwise identifications on triple overlaps, in
  the source `LinearEquiv.trans` presentation. -/
  cocycle : AwayModuleGlueingCocycleCondition f localModule overlapIso

namespace AwayModuleGlueing

variable {f : Fin n → R} (glue : AwayModuleGlueing f)

/-! The chapter datum keeps its source-facing `LinearEquiv.trans` cocycle and
the finite `Fin n` presentation.  The following view exposes the same
concrete local pieces and overlap maps through the generalized ReasLib owner;
the cocycle conversion is proposition-valued because the two presentations
normalize triple products differently. -/

/-- The concrete pregluing view of a chapter datum in the
generalized principal-open gluing owner. -/
@[stacks 00EK "source datum to generalized pregluing view"]
def toPreGluing : LocalizedModule.Away.PreGluing f :=
  { localModule := glue.localModule
    overlapIso := glue.overlapIso }

/-- The source `LinearEquiv.trans` cocycle transports to the
canonical `LinearMap.comp` cocycle after the owner normalizes triple overlaps. -/
theorem toPreGluing_cocycle :
    LocalizedModule.Away.PreGluing.CocycleCondition glue.toPreGluing := sorry

/-- Canonical ReasLib gluing data associated to a source datum.
The local pieces and overlap isomorphisms are explicit; only the converted
cocycle is deferred. -/
@[stacks 00EK "source datum to canonical gluing data"]
def toGluing : LocalizedModule.Away.Gluing f :=
  { toPreGluing := glue.toPreGluing
    cocycle := glue.toPreGluing_cocycle }

/-- The canonical view of source gluing data has the original local module. -/
@[simp, stacks 00EK "source/canonical gluing local module"]
theorem toGluing_localModule (i : Fin n) :
    glue.toGluing.localModule i = glue.localModule i := sorry

/-- The canonical view of source gluing data has the original overlap
isomorphism. -/
@[simp, stacks 00EK "source/canonical gluing overlap isomorphism"]
theorem toGluing_overlapIso (i j : Fin n) :
    glue.toGluing.overlapIso i j = glue.overlapIso i j := sorry

/-- The canonical cocycle implies the source `LinearEquiv.trans` cocycle after
normalizing the three triple-overlap transports. -/
theorem ofGluing_cocycle (data : LocalizedModule.Away.Gluing f) :
    AwayModuleGlueingCocycleCondition f data.localModule data.overlapIso := sorry

/-- The source view of canonical finite principal-open gluing data.  It reuses
the local modules and overlap isomorphisms without choosing new data. -/
@[stacks 00EK "canonical gluing datum to source datum"]
def ofGluing (data : LocalizedModule.Away.Gluing f) : AwayModuleGlueing f where
  localModule := data.localModule
  overlapIso := data.overlapIso
  cocycle := ofGluing_cocycle data

/-- The source view of canonical gluing data has the original local module. -/
@[simp, stacks 00EK "canonical/source gluing local module"]
theorem ofGluing_localModule (data : LocalizedModule.Away.Gluing f) (i : Fin n) :
    (ofGluing data).localModule i = data.localModule i := sorry

/-- The source view of canonical gluing data has the original overlap
isomorphism. -/
@[simp, stacks 00EK "canonical/source gluing overlap isomorphism"]
theorem ofGluing_overlapIso
    (data : LocalizedModule.Away.Gluing f) (i j : Fin n) :
    (ofGluing data).overlapIso i j = data.overlapIso i j := sorry

/-- Passing source gluing data to the canonical owner and back recovers the
source datum. -/
@[simp, stacks 00EK "source/canonical gluing datum left inverse"]
theorem ofGluing_toGluing (data : AwayModuleGlueing f) :
    ofGluing data.toGluing = data := sorry

/-- Passing canonical finite gluing data to the source view and back recovers
the canonical datum. -/
@[simp, stacks 00EK "source/canonical gluing datum right inverse"]
theorem toGluing_ofGluing (data : LocalizedModule.Away.Gluing f) :
    (ofGluing data).toGluing = data := sorry

/-- Each local piece is already localized away from its defining element. -/
instance localizedInstance (glue : AwayModuleGlueing f) (i : Fin n) :
    IsLocalizedModule.Away (f i)
      (LinearMap.id : glue.localModule i →ₗ[R] glue.localModule i) := sorry

/-- The compatibility map whose kernel is the glued module. Its `(i,j)`-component is
`m_i/1 - ψ_{ij}^{-1}(m_j/1)`.  The explicit source formula preserves the
`Module` instance path used by downstream kernel computations; the theorem
`toGluing_compatibilityMap` supplies the propositional bridge to the canonical
owner. -/
noncomputable def compatibilityMap (glue : AwayModuleGlueing f) :
    (∀ i : Fin n, glue.localModule i) →ₗ[R]
      ∀ i : Fin n, ∀ j : Fin n, Away (f i * f j) (glue.localModule i) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j)) (glue.localModule i)).comp
        (LinearMap.proj i) -
      (((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm.toLinearMap).comp
        ((LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j)) (glue.localModule j)).comp
          (LinearMap.proj j))

/-- The `(i,j)` component of the source compatibility map is the difference
of the two restrictions to the common principal overlap. -/
@[simp, stacks 00EK "source gluing compatibility component"]
theorem compatibilityMap_apply
    (glue : AwayModuleGlueing f) (x : ∀ i : Fin n, glue.localModule i) (i j : Fin n) :
    glue.compatibilityMap x i j =
      LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j))
          (glue.localModule i) (x i) -
        ((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm
          (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j))
            (glue.localModule j) (x j)) := sorry

/-- The glued module attached to an affine localization gluing datum. -/
def gluedModule (glue : AwayModuleGlueing f) : Submodule R (∀ i : Fin n, glue.localModule i) :=
  LinearMap.ker glue.compatibilityMap

/-- A source family belongs to the glued module exactly when its two local
sections agree on every pairwise principal overlap. -/
@[stacks 00EK "source glued-module membership"]
theorem mem_gluedModule_iff
    (glue : AwayModuleGlueing f) (x : ∀ i : Fin n, glue.localModule i) :
    x ∈ glue.gluedModule ↔
      ∀ i j : Fin n,
        LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j))
            (glue.localModule i) (x i) =
          ((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm
            (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j))
              (glue.localModule j) (x j)) := sorry

/-- The natural projection from the glued module to the `i`-th local module, viewed over `R`. -/
def projection (glue : AwayModuleGlueing f) (i : Fin n) : glue.gluedModule →ₗ[R] glue.localModule i :=
  (LinearMap.proj i).comp glue.gluedModule.subtype

/-- The source projection evaluates a compatible family at its `i`-th
coordinate. -/
@[simp, stacks 00EK "source glued-module projection application"]
theorem projection_apply
    (glue : AwayModuleGlueing f) (i : Fin n) (m : glue.gluedModule) :
    glue.projection i m = m.1 i := sorry

/-- The localized projection map in the source-facing category of `R_(fᵢ)`-modules. -/
noncomputable def localizedProjection (glue : AwayModuleGlueing f) (i : Fin n) :
    Away (f i) glue.gluedModule →ₗ[Localization.Away (f i)] glue.localModule i :=
  (IsLocalizedModule.map (Submonoid.powers (f i))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) glue.gluedModule)
      (LinearMap.id : glue.localModule i →ₗ[R] glue.localModule i)
      (glue.projection i)).extendScalarsOfIsLocalization
    (Submonoid.powers (f i)) (Localization.Away (f i))

/-- The source localized projection sends a canonical localized compatible
family to its corresponding local coordinate. -/
@[simp, stacks 00EK "source localized projection application"]
theorem localizedProjection_apply_mk
    (glue : AwayModuleGlueing f) (i : Fin n) (m : glue.gluedModule) :
    glue.localizedProjection i
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) glue.gluedModule m) =
      glue.projection i m := sorry

/-! The finite chapter presentation also needs a morphism layer for the
formal-glueing category in Chapter 15.  Its record fields preserve the source
constructor and reduction behavior; `toGluingHom` exposes the same maps and
overlap squares through the generalized ReasLib owner. -/

/-- A source-facing morphism between finite principal-open gluing data.  The
local maps are concrete and the overlap naturality squares are propositional. -/
@[stacks 00EK "source finite gluing morphism"]
structure Hom {f : Fin n → R} (X Y : AwayModuleGlueing f) where
  /-- The map on each localized local module. -/
  localMap : ∀ i : Fin n, X.localModule i ⟶ Y.localModule i
  /-- Naturality of the local maps on every pairwise overlap. -/
  overlap_comm : ∀ i j : Fin n,
    CommSq
      (ModuleCat.ofHom <| LocalizedModule.map (Submonoid.powers (f i * f j))
        ((localMap i).hom.restrictScalars R))
      (X.overlapIso i j).hom
      (Y.overlapIso i j).hom
      (ModuleCat.ofHom <| LocalizedModule.map (Submonoid.powers (f i * f j))
        ((localMap j).hom.restrictScalars R))

namespace Hom

variable {f : Fin n → R} {X Y : AwayModuleGlueing f}

/-- The generalized ReasLib morphism determined by a source gluing morphism.
The local maps and overlap squares are reused without choosing new data. -/
@[stacks 00EK "source morphism to generalized gluing morphism"]
def toGluingHom (φ : Hom X Y) :
    LocalizedModule.Away.Gluing.Hom X.toGluing Y.toGluing where
  hom := φ.localMap
  comm := φ.overlap_comm

/-- The canonical morphism view has the original map on every local piece. -/
@[simp, stacks 00EK "source/canonical gluing morphism local map"]
theorem toGluingHom_hom (φ : Hom X Y) (i : Fin n) :
    φ.toGluingHom.hom i = φ.localMap i := sorry

/-- The coordinatewise family map underlying a source gluing morphism. -/
@[stacks 00EK "source gluing morphism family map"]
def familyMap (φ : Hom X Y) :
    (∀ i : Fin n, X.localModule i) →ₗ[R] ∀ i : Fin n, Y.localModule i :=
  φ.toGluingHom.familyMap

/-- The family map of a source gluing morphism acts coordinatewise by its
specified local maps. -/
@[simp, stacks 00EK "source gluing morphism family map application"]
theorem familyMap_apply (φ : Hom X Y)
    (x : ∀ i : Fin n, X.localModule i) (i : Fin n) :
    φ.familyMap x i = φ.localMap i (x i) := sorry

/-- The family map preserves the source compatible-family kernel. -/
@[stacks 00EK "source gluing morphism preserves glued module"]
theorem familyMap_mem_gluedModule (φ : Hom X Y)
    (x : ∀ i : Fin n, X.localModule i) (hx : x ∈ X.gluedModule) :
    φ.familyMap x ∈ Y.gluedModule := sorry

/-- The induced concrete linear map on source glued modules. -/
@[stacks 00EK "source gluing morphism induced map"]
noncomputable def gluedMap (φ : Hom X Y) : X.gluedModule →ₗ[R] Y.gluedModule :=
  (φ.familyMap.comp X.gluedModule.subtype).codRestrict Y.gluedModule
    (fun x ↦ φ.familyMap_mem_gluedModule x.1 x.2)

/-- The induced source glued-module map acts on every coordinate by the
corresponding local map. -/
@[simp, stacks 00EK "source gluing morphism coordinate application"]
theorem gluedMap_apply (φ : Hom X Y) (x : X.gluedModule) (i : Fin n) :
    (φ.gluedMap x).1 i = φ.localMap i (x.1 i) := sorry

/-- The induced source glued-module map has the prescribed local component.
This is the finite source-facing bridge to
`LocalizedModule.Away.Gluing.Hom.projection_gluedMap`. -/
@[stacks 00EK "source gluing morphism projection"]
theorem projection_gluedMap (φ : Hom X Y) (i : Fin n) :
    (Y.projection i).comp φ.gluedMap =
      ((φ.localMap i).hom.restrictScalars R).comp (X.projection i) := sorry

/-- Localizing the induced source glued-module map commutes with the local
projection on every member of the finite principal-open family. -/
@[stacks 00EK "source gluing morphism localized projection naturality"]
theorem localizedProjection_naturality (φ : Hom X Y) (i : Fin n) :
    (Y.localizedProjection i).comp
        (LocalizedModule.map (Submonoid.powers (f i)) φ.gluedMap) =
      (φ.localMap i).hom.comp (X.localizedProjection i) := sorry

/-- Two source gluing morphisms are equal when their local maps agree. -/
@[ext, stacks 00EK "source gluing morphism extensionality"]
theorem ext {φ ψ : Hom X Y} (hlocal : ∀ i : Fin n, φ.localMap i = ψ.localMap i) :
    φ = ψ := sorry

/-- The identity overlap squares for a source gluing datum. -/
theorem id_overlap_comm (X : AwayModuleGlueing f) :
    ∀ i j : Fin n,
      CommSq
        (ModuleCat.ofHom <| LocalizedModule.map (Submonoid.powers (f i * f j))
          (LinearMap.id : X.localModule i →ₗ[R] X.localModule i))
        (X.overlapIso i j).hom
        (X.overlapIso i j).hom
        (ModuleCat.ofHom <| LocalizedModule.map (Submonoid.powers (f i * f j))
          (LinearMap.id : X.localModule j →ₗ[R] X.localModule j)) := sorry

/-- The identity source gluing morphism. -/
@[stacks 00EK "source gluing identity morphism"]
def id (X : AwayModuleGlueing f) : Hom X X where
  localMap := fun i ↦ 𝟙 (X.localModule i)
  overlap_comm := id_overlap_comm X

/-- The local component of the identity source gluing morphism is the
identity map. -/
@[simp, stacks 00EK "source gluing identity component"]
theorem id_localMap (X : AwayModuleGlueing f) (i : Fin n) :
    (id X).localMap i = 𝟙 (X.localModule i) := sorry

/-- The composite overlap squares for source gluing morphisms. -/
theorem comp_overlap_comm
    {X Y Z : AwayModuleGlueing f} (φ : Hom X Y) (ψ : Hom Y Z) :
    ∀ i j : Fin n,
      CommSq
        (ModuleCat.ofHom <| LocalizedModule.map (Submonoid.powers (f i * f j))
          ((φ.localMap i ≫ ψ.localMap i).hom.restrictScalars R))
        (X.overlapIso i j).hom
        (Z.overlapIso i j).hom
        (ModuleCat.ofHom <| LocalizedModule.map (Submonoid.powers (f i * f j))
          ((φ.localMap j ≫ ψ.localMap j).hom.restrictScalars R)) := sorry

/-- The composite source gluing morphism. -/
@[stacks 00EK "source gluing composition morphism"]
def comp {X Y Z : AwayModuleGlueing f} (φ : Hom X Y) (ψ : Hom Y Z) : Hom X Z where
  localMap := fun i ↦ φ.localMap i ≫ ψ.localMap i
  overlap_comm := comp_overlap_comm φ ψ

/-- The local component of a composite source gluing morphism is the
composite of its local components. -/
@[simp, stacks 00EK "source gluing composition component"]
theorem comp_localMap
    {X Y Z : AwayModuleGlueing f} (φ : Hom X Y) (ψ : Hom Y Z) (i : Fin n) :
    (comp φ ψ).localMap i = φ.localMap i ≫ ψ.localMap i := sorry

/-- Left identity for source gluing morphisms. -/
theorem id_comp {X Y : AwayModuleGlueing f} (φ : Hom X Y) :
    comp (id X) φ = φ := sorry

/-- Right identity for source gluing morphisms. -/
theorem comp_id {X Y : AwayModuleGlueing f} (φ : Hom X Y) :
    comp φ (id Y) = φ := sorry

/-- Associativity for source gluing morphisms. -/
theorem assoc {W X Y Z : AwayModuleGlueing f}
    (φ : Hom W X) (ψ : Hom X Y) (χ : Hom Y Z) :
    comp (comp φ ψ) χ = comp φ (comp ψ χ) := sorry

/-- The glued-module map induced by the identity source morphism is the
identity linear map. -/
@[simp, stacks 00EK "source gluing identity induced map"]
theorem gluedMap_id (X : AwayModuleGlueing f) :
    (id X).gluedMap = LinearMap.id := sorry

/-- The glued-module map induced by a composite source morphism is the
composite of the induced glued-module maps. -/
@[simp, stacks 00EK "source gluing composition induced map"]
theorem gluedMap_comp {X Y Z : AwayModuleGlueing f} (φ : Hom X Y) (ψ : Hom Y Z) :
    (comp φ ψ).gluedMap = ψ.gluedMap.comp φ.gluedMap := sorry

/-- The generalized morphism view sends the source identity to the canonical
identity gluing morphism. -/
theorem toGluingHom_id (X : AwayModuleGlueing f) :
    (id X).toGluingHom = LocalizedModule.Away.Gluing.Hom.id X.toGluing := sorry

/-- The generalized morphism view sends source composition to canonical
composition in the same order. -/
theorem toGluingHom_comp
    {X Y Z : AwayModuleGlueing f} (φ : Hom X Y) (ψ : Hom Y Z) :
    (comp φ ψ).toGluingHom =
      LocalizedModule.Away.Gluing.Hom.comp φ.toGluingHom ψ.toGluingHom := sorry

/-- The source morphism associated to a canonical gluing morphism.  The local
maps and overlap squares are reused without transport or choice. -/
@[stacks 00EK "canonical gluing morphism to source morphism"]
def ofGluingMap
    {X Y : LocalizedModule.Away.Gluing f}
    (φ : X ⟶ Y) : Hom (ofGluing X) (ofGluing Y) where
  localMap := φ.hom
  overlap_comm := φ.comm

/-- The source morphism view has the original canonical map on every local piece. -/
@[simp, stacks 00EK "canonical/source gluing morphism local map"]
theorem ofGluingMap_localMap
    {X Y : LocalizedModule.Away.Gluing f} (φ : X ⟶ Y) (i : Fin n) :
    (ofGluingMap φ).localMap i = φ.hom i := sorry

/-- The source morphism associated to a canonical identity is the source
identity. -/
theorem ofGluingMap_id (X : LocalizedModule.Away.Gluing f) :
    ofGluingMap (𝟙 X) = id (ofGluing X) := sorry

/-- The source morphism view preserves composition of canonical gluing
morphisms. -/
theorem ofGluingMap_comp
    {X Y Z : LocalizedModule.Away.Gluing f} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    ofGluingMap (φ ≫ ψ) = comp (ofGluingMap φ) (ofGluingMap ψ) := sorry

end Hom

/-- The source finite gluing data form a category under local-map morphisms. -/
@[stacks 00EK "source finite gluing category"]
instance instCategory {f : Fin n → R} : Category (AwayModuleGlueing f) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The source finite gluing category maps canonically to the generalized
principal-open gluing category by preserving its concrete local pieces and
overlap morphisms. -/
@[stacks 00EK "source finite gluing to generalized gluing functor"]
def toGluingFunctor (f : Fin n → R) :
    AwayModuleGlueing f ⥤ LocalizedModule.Away.Gluing f where
  obj X := X.toGluing
  map φ := φ.toGluingHom
  map_id X := Hom.toGluingHom_id X
  map_comp φ ψ := Hom.toGluingHom_comp φ ψ

/-- The source-to-canonical functor sends a source datum to its named
canonical gluing view. -/
@[simp, stacks 00EK "source finite gluing functor object"]
theorem toGluingFunctor_obj (f : Fin n → R) (X : AwayModuleGlueing f) :
    (toGluingFunctor f).obj X = X.toGluing := sorry

/-- The source-to-canonical functor sends a source morphism to its named
canonical morphism view. -/
@[simp, stacks 00EK "source finite gluing functor map"]
theorem toGluingFunctor_map
    {f : Fin n → R} {X Y : AwayModuleGlueing f} (φ : X ⟶ Y) :
    (toGluingFunctor f).map φ = φ.toGluingHom := sorry

/-- The canonical-to-source functor reuses the local modules, overlap
isomorphisms, and compatible local morphisms of canonical gluing data. -/
@[stacks 00EK "canonical gluing to source finite gluing functor"]
def ofGluingFunctor (f : Fin n → R) :
    LocalizedModule.Away.Gluing f ⥤ AwayModuleGlueing f where
  obj X := ofGluing X
  map φ := Hom.ofGluingMap φ
  map_id := Hom.ofGluingMap_id
  map_comp := Hom.ofGluingMap_comp

/-- The canonical-to-source functor sends canonical gluing data to its named
source view. -/
@[simp, stacks 00EK "canonical gluing functor object"]
theorem ofGluingFunctor_obj
    (f : Fin n → R) (X : LocalizedModule.Away.Gluing f) :
    (ofGluingFunctor f).obj X = ofGluing X := sorry

/-- The canonical-to-source functor sends a canonical morphism to its named
source morphism view. -/
@[simp, stacks 00EK "canonical gluing functor map"]
theorem ofGluingFunctor_map
    {f : Fin n → R} {X Y : LocalizedModule.Away.Gluing f} (φ : X ⟶ Y) :
    (ofGluingFunctor f).map φ = Hom.ofGluingMap φ := sorry

/-- Naturality of the objectwise source/canonical left-inverse
identifications. -/
theorem toGluingUnitIso_naturality
    {X Y : AwayModuleGlueing f} (φ : X ⟶ Y) :
    φ ≫ (eqToIso (ofGluing_toGluing Y).symm).hom =
      (eqToIso (ofGluing_toGluing X).symm).hom ≫
        (ofGluingFunctor f).map ((toGluingFunctor f).map φ) := sorry

/-- The identity source functor is naturally isomorphic to passage to the
canonical gluing owner followed by the explicit source view. -/
def toGluingUnitIso (f : Fin n → R) :
    𝟭 (AwayModuleGlueing f) ≅ toGluingFunctor f ⋙ ofGluingFunctor f :=
  NatIso.ofComponents (fun X ↦ eqToIso (ofGluing_toGluing X).symm)
    (fun φ ↦ toGluingUnitIso_naturality φ)

/-- Naturality of the objectwise canonical/source right-inverse
identifications. -/
theorem toGluingCounitIso_naturality
    {X Y : LocalizedModule.Away.Gluing f} (φ : X ⟶ Y) :
    (toGluingFunctor f).map ((ofGluingFunctor f).map φ) ≫
        (eqToIso (toGluing_ofGluing Y)).hom =
      (eqToIso (toGluing_ofGluing X)).hom ≫ φ := sorry

/-- Passage to the explicit source view and back is naturally isomorphic to
the identity canonical gluing functor. -/
def toGluingCounitIso (f : Fin n → R) :
    ofGluingFunctor f ⋙ toGluingFunctor f ≅
      𝟭 (LocalizedModule.Away.Gluing f) :=
  NatIso.ofComponents (fun X ↦ eqToIso (toGluing_ofGluing X))
    (fun φ ↦ toGluingCounitIso_naturality φ)

/-- The explicit source/canonical unit and counit satisfy the equivalence
triangle identity. -/
theorem toGluingEquivalence_triangle (f : Fin n → R)
    (X : AwayModuleGlueing f) :
    (toGluingFunctor f).map ((toGluingUnitIso f).hom.app X) ≫
        (toGluingCounitIso f).hom.app ((toGluingFunctor f).obj X) =
      𝟙 ((toGluingFunctor f).obj X) := sorry

/-- The concrete source presentation and the canonical ReasLib presentation
of finite principal-open gluing data are explicitly equivalent categories. -/
@[stacks 00EK "source/canonical finite gluing category equivalence"]
def toGluingEquivalence (f : Fin n → R) :
    AwayModuleGlueing f ≌ LocalizedModule.Away.Gluing f where
  functor := toGluingFunctor f
  inverse := ofGluingFunctor f
  unitIso := toGluingUnitIso f
  counitIso := toGluingCounitIso f
  functor_unitIso_comp := toGluingEquivalence_triangle f

/-- The source and canonical finite-index gluing categories are equivalent
through the standard Mathlib `Functor.IsEquivalence` interface. -/
@[stacks 00EK "source finite gluing functor equivalence"]
instance toGluingFunctorIsEquivalence (f : Fin n → R) :
    (toGluingFunctor f).IsEquivalence :=
  (toGluingEquivalence f).isEquivalence_functor

#check @LocalizedModule.Away.Gluing.Hom
#check @AwayModuleGlueing.Hom.familyMap_apply
#check @AwayModuleGlueing.Hom.gluedMap_apply
#check @AwayModuleGlueing.Hom.id_localMap
#check @AwayModuleGlueing.Hom.comp_localMap
#check @AwayModuleGlueing.toGluingFunctor_obj
#check @AwayModuleGlueing.toGluingFunctor_map
#check @AwayModuleGlueing.ofGluingFunctor_obj
#check @AwayModuleGlueing.ofGluingFunctor_map
#print axioms AwayModuleGlueing.Hom
#print axioms AwayModuleGlueing.Hom.familyMap
#print axioms AwayModuleGlueing.Hom.gluedMap
#print axioms AwayModuleGlueing.toGluingFunctor
#print axioms AwayModuleGlueing.ofGluingFunctor
#print axioms AwayModuleGlueing.toGluingEquivalence

/-- The owner compatibility map agrees with the source
kernel-map presentation. -/
@[stacks 00EK "source/canonical compatibility-map bridge"]
theorem toGluing_compatibilityMap :
    glue.toGluing.compatibilityMap = glue.compatibilityMap := sorry

/-- The owner equalizer module agrees with the source kernel
module after the compatibility-map bridge. -/
@[stacks 00EK "source/canonical glued-module bridge"]
theorem toGluing_gluedModule :
    glue.toGluing.gluedModule = glue.gluedModule := sorry

/-- Dependent type cast from the owner localized carrier to the
source kernel carrier.  This is a named Prop bridge so consumers do not expose
raw equality recursors. -/
@[stacks 00EQ "source local recovery equivalence"]
theorem toGluing_localizedProjection_type (i : Fin n) :
    (Away (f i) glue.toGluing.gluedModule ≃ₗ[Localization.Away (f i)] glue.localModule i) =
      (Away (f i) glue.gluedModule ≃ₗ[Localization.Away (f i)] glue.localModule i) := sorry

#print axioms AwayModuleGlueing.toPreGluing
#print axioms AwayModuleGlueing.toGluing
#print axioms AwayModuleGlueing.ofGluing
#print axioms AwayModuleGlueing
#print axioms AwayModuleGlueing.compatibilityMap
#print axioms AwayModuleGlueing.gluedModule
#print axioms AwayModuleGlueing.localizedProjection

/-- Historical source name for the canonical identity-localization
equivalence on the `i`-th local piece.  The local instance is pinned to the
proof-independent pregluing owner so this datum does not inherit the deferred
source compatibility instance. -/
noncomputable abbrev localModuleAwayEquiv (glue : AwayModuleGlueing f) (i : Fin n) :
    Away (f i) (glue.localModule i) ≃ₗ[R] glue.localModule i :=
  letI : IsLocalizedModule (Submonoid.powers (f i))
      (LinearMap.id : glue.localModule i →ₗ[R] glue.localModule i) :=
    glue.toPreGluing.localModule_isLocalized i
  LocalizedModule.Away.idLinearEquiv (f i)

/-- The source collapse equivalence agrees with the canonical identity-localization
equivalence for the local piece. -/
theorem localModuleAwayEquiv_eq_idLinearEquiv
    (glue : AwayModuleGlueing f) (i : Fin n) :
    glue.localModuleAwayEquiv i = LocalizedModule.Away.idLinearEquiv (f i) := sorry

/-- Helper for Lemma 10.24.5: the distinguished coordinate map is bijective on the standard
unit-case kernel attached to `glue.localModule i`. -/
noncomputable abbrev standardKernelCoordinate
    (glue : AwayModuleGlueing f) (i : Fin n) :
    LinearMap.ker (awayLocalizationCompatibilityMap (M := glue.localModule i) f) →ₗ[R]
      glue.localModule i :=
  (glue.localModuleAwayEquiv i).toLinearMap.comp
    ((LinearMap.proj i).comp
      (LinearMap.ker (awayLocalizationCompatibilityMap (M := glue.localModule i) f)).subtype)

/-- Helper for Lemma 10.24.5: the standard unit-case kernel coordinate map is bijective. -/
theorem standard_kernel_coordinate_bijective
    (glue : AwayModuleGlueing f) (i : Fin n) :
    Function.Bijective (glue.standardKernelCoordinate i) := sorry

/-- Helper for Lemma 10.24.5: after localizing the `j`-th local piece once more away from `f i`,
the overlap isomorphism identifies it with the `j`-th standard localization of the `i`-th piece. -/
noncomputable abbrev local_piece_overlap_equiv
    (glue : AwayModuleGlueing f) (i j : Fin n) :
    Away (f i) (glue.localModule j) ≃ₗ[R] Away (f j) (glue.localModule i) :=
  -- First reinsert the trivial `f j`-localization on the `j`-piece, then swap the localization
  -- order, transport across the overlap isomorphism, and finally collapse the trivial
  -- `f i`-localization on the `i`-piece.
  (awayLocalizeLinearEquiv (f i) (glue.localModuleAwayEquiv j).symm).trans
    ((awayMulLinearEquiv (f j) (f i) (glue.localModule j)).trans
      ((awayEqLinearEquiv (glue.localModule j) (mul_comm (f j) (f i))).trans
        ((((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm).trans
          (((awayMulLinearEquiv (f i) (f j) (glue.localModule i)).symm).trans
            (awayLocalizeLinearEquiv (f j) (glue.localModuleAwayEquiv i))))))

/-- Helper for Lemma 10.24.5: after localizing the middle product away from `f i`, the pairwise
overlap transports identify it with the standard middle term for `glue.localModule i`. -/
noncomputable abbrev localized_middle_comparison
    (glue : AwayModuleGlueing f) (i : Fin n) :
    Away (f i) (∀ j : Fin n, glue.localModule j) ≃ₗ[R]
      ∀ j : Fin n, Away (f j) (glue.localModule i) :=
  -- First use the canonical finite-product localization comparison, then
  -- transport each coordinate through the corresponding overlap equivalence.
  ((LocalizedModule.piLinearEquiv (.powers (f i))
      (fun j ↦ glue.localModule j)).restrictScalars R).trans
    (LinearEquiv.piCongrRight fun j ↦ glue.local_piece_overlap_equiv i j)

/-- Helper for Lemma 10.24.5: the middle comparison sends a canonical localized family to the
family obtained by applying the pairwise overlap identifications coordinatewise. -/
@[simp]
theorem localized_middle_comparison_apply_mk_one
    (glue : AwayModuleGlueing f) (i j : Fin n) (x : ∀ j : Fin n, glue.localModule j) :
    (glue.localized_middle_comparison i (LocalizedModule.mk x 1)) j =
      glue.local_piece_overlap_equiv i j (LocalizedModule.mk (x j) 1) := sorry

/-- Helper for Lemma 10.24.5: the target-side component comparison first rewrites the iterated
localization on the `j`-piece into the common triple overlap. -/
theorem localized_target_component_domain_eq
    (i j k : Fin n) :
    (f j * f k) * f i = f i * f j * f k := sorry

/-- Helper for Lemma 10.24.5: the target-side component comparison ends by viewing the common
triple overlap as a localization of the `i`-piece away from `f_j f_k`. -/
theorem localized_target_component_codomain_eq
    (i j k : Fin n) :
    f i * f j * f k = f i * (f j * f k) := sorry

/-- Helper for Lemma 10.24.5: after localizing the `(j,k)` target component once more away from
`f i`, the cocycle datum transports it to the standard `(j,k)` target component on the fixed
`i`-piece. -/
noncomputable abbrev localized_target_component_equiv
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    Away (f i) (Away (f j * f k) (glue.localModule j)) ≃ₗ[R]
      Away (f j * f k) (glue.localModule i) :=
  -- Move to the triple overlap on the `j`-piece, transport across the cocycle comparison to the
  -- `i`-piece, and then collapse the trivial `f i`-localization on the fixed local piece.
  (awayMulLinearEquiv (f j * f k) (f i) (glue.localModule j)).trans
    ((awayEqLinearEquiv (glue.localModule j)
        (AwayModuleGlueing.localized_target_component_domain_eq (f := f) i j k)).trans
      (((awayModuleGlueingTripleOverlapHom12 f glue.localModule glue.overlapIso i j k).symm).trans
        ((awayEqLinearEquiv (glue.localModule i)
            (AwayModuleGlueing.localized_target_component_codomain_eq (f := f) i j k)).trans
          (((awayMulLinearEquiv (f i) (f j * f k) (glue.localModule i)).symm).trans
            (awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i))))))

/-- The source denominator transport agrees with the canonical iterated-localization owner. -/
theorem awayEqLinearEquiv_eq_denominatorEquiv
    (M : Type v) [AddCommGroup M] [Module R M] {a b : R} (h : a = b) :
    awayEqLinearEquiv M h =
      LocalizedModule.Away.Iterated.denominatorEquiv M h := sorry

/-- The source successive-localization equivalence agrees with the canonical
product-localization equivalence. -/
theorem awayMulLinearEquiv_eq_baseMulEquiv
    (a b : R) (M : Type v) [AddCommGroup M] [Module R M] :
    awayMulLinearEquiv a b M =
      LocalizedModule.Away.Iterated.baseMulEquiv a b M := sorry

/-- Historical source spelling of `awayModuleEnd_isUnit_of_dvd`, retained by
the explicit target-branch normal forms for Lemma 10.24.5. -/
theorem away_module_end_isUnit_of_dvd
    (M : Type v) [AddCommGroup M] [Module R M] (x r : R) (h : r ∣ x) :
    IsUnit (algebraMap R (Module.End R (Away x M)) r) := sorry

/-- Helper for Lemma 10.24.5: the iterated-localization comparison sends a double canonical
   generator to the corresponding direct-localization generator. -/
@[simp]
theorem awayMulLinearEquiv_apply_mk_mk
    (a b : R) (M : Type v) [AddCommGroup M] [Module R M] (m : M) :
    (awayMulLinearEquiv a b M) (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
      LocalizedModule.mk m 1 := sorry

/-- Helper for Lemma 10.24.5: the inverse iterated-localization comparison sends a canonical
   generator to the corresponding double canonical generator. -/
@[simp]
theorem awayMulLinearEquiv_symm_apply_mk_one
    (a b : R) (M : Type v) [AddCommGroup M] [Module R M] (m : M) :
    (awayMulLinearEquiv a b M).symm (LocalizedModule.mk m 1) =
      LocalizedModule.mk (LocalizedModule.mk m 1) 1 := sorry

#print axioms AwayModuleGlueing.localModuleAwayEquiv

/-- Helper for Lemma 10.24.5: collapsing the trivial localization on the `i`-th local piece sends
`m/1` back to `m`. -/
@[simp]
theorem localModuleAwayEquiv_apply_mk_one
    (glue : AwayModuleGlueing f) (i : Fin n) (x : glue.localModule i) :
    glue.localModuleAwayEquiv i (LocalizedModule.mk x 1) = x := sorry

/-- Helper for Lemma 10.24.5: after localizing the target product away from `f i`, the cocycle
transport identifies it with the standard target product for the fixed `i`-th local piece. -/
noncomputable abbrev localized_target_comparison
    (glue : AwayModuleGlueing f) (i : Fin n) :
    Away (f i) (∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule j)) ≃ₗ[R]
      ∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule i) :=
  -- First compare the localized target family with the coordinatewise localized target
  -- components, then transport each `(j,k)` coordinate through the triple-overlap equivalence.
  let outerComparison :
      Away (f i) (∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule j)) ≃ₗ[R]
        ∀ j : Fin n, Away (f i) (∀ k : Fin n, Away (f j * f k) (glue.localModule j)) :=
    (LocalizedModule.piLinearEquiv (.powers (f i))
      (fun j ↦ ∀ k : Fin n, Away (f j * f k) (glue.localModule j))).restrictScalars R
  let rowComparison :
      (∀ j : Fin n, Away (f i) (∀ k : Fin n, Away (f j * f k) (glue.localModule j))) ≃ₗ[R]
        ∀ j : Fin n, ∀ k : Fin n, Away (f i) (Away (f j * f k) (glue.localModule j)) :=
    LinearEquiv.piCongrRight fun j ↦
      (LocalizedModule.piLinearEquiv (.powers (f i))
        (fun k ↦ Away (f j * f k) (glue.localModule j))).restrictScalars R
  let componentComparison :
      (∀ j : Fin n, ∀ k : Fin n, Away (f i) (Away (f j * f k) (glue.localModule j))) ≃ₗ[R]
        ∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule i) :=
    LinearEquiv.piCongrRight fun j ↦
      LinearEquiv.piCongrRight fun k ↦ glue.localized_target_component_equiv i j k
  outerComparison.trans (rowComparison.trans componentComparison)

/-- Helper for Lemma 10.24.5: the packaged target comparison sends a canonical localized target
family to the family obtained by applying the target-side cocycle transports coordinatewise. -/
@[simp]
theorem localized_target_comparison_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n)
    (x : ∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule j)) :
    ((glue.localized_target_comparison i (LocalizedModule.mk x 1)) j) k =
      glue.localized_target_component_equiv i j k
        (LocalizedModule.mk (x j k) 1) := sorry

#print axioms AwayModuleGlueing.localized_middle_comparison
#print axioms AwayModuleGlueing.standardKernelCoordinate
#print axioms AwayModuleGlueing.local_piece_overlap_equiv
#print axioms AwayModuleGlueing.localized_target_component_equiv
#print axioms AwayModuleGlueing.localized_target_comparison

end AwayModuleGlueing

end
