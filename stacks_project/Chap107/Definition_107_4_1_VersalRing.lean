/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap98.«98_3_0_1_Factorization»
public import stacks_project.Chap98.«98_9_3_1_Approximation»
public import stacks_project.Chap98.Definition_98_13_1_Versal
public import stacks_project.Chap100.Lemma_100_4_1_FieldValuedPoint
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap107.Situation_107_2_1_Instances

/-!
# Versal rings of algebraic stacks at finite type points

A complete local `S`-algebra `A` is a versal ring to an algebraic stack `X` at a
finite type field-valued point `x0` when it carries a versal formal object of
`X` whose first stage is 2-isomorphic to `x0`. The object-level locally of
finite type hypothesis is Situation 107.2.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing
open FiberedCategoryOver.Groupoids
open scoped Bicategory BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.CompleteLocalSAlgebra

variable {S : Scheme.{u}}

/-- Canonical morphism `Spec(κ(A)) ⟶ Spec(A)` induced by the residue map. -/
def residueToSpec (A : CompleteLocalSAlgebra S) :
    Spec (CommRingCat.of (ResidueField A.carrier)) ⟶
      Spec (CommRingCat.of A.carrier) :=
  Spec.map (CommRingCat.ofHom (residue A.carrier))

/-- Structure morphism `Spec(κ(A)) ⟶ S` of the residue field of `A`. -/
def residueToS (A : CompleteLocalSAlgebra S) :
    Spec (CommRingCat.of (ResidueField A.carrier)) ⟶ S :=
  A.residueToSpec ≫ A.toS

/-- `residueToS` is the residue-field spectrum of `A` over `S`. -/
theorem residueToS_eq (A : CompleteLocalSAlgebra S) :
    A.residueToS =
      Spec.map (CommRingCat.ofHom (residue A.carrier)) ≫ A.toS := sorry

/-- The residue-field point of a complete local `S`-algebra remains locally of
finite type over `S`. -/
instance instLocallyOfFiniteType_residueToS (A : CompleteLocalSAlgebra S) :
    LocallyOfFiniteType A.residueToS :=
  A.residue_locallyOfFiniteType

/-- Residue morphism `Spec(κ(A)) ⟶ Spec(A)` in `Over S`. -/
def residueOverHom (A : CompleteLocalSAlgebra S) :
    Over.mk A.residueToS ⟶ Over.mk A.toS :=
  Over.homMk A.residueToSpec rfl

/-- The underlying scheme morphism of `residueOverHom` is `residueToSpec`. -/
theorem residueOverHom_left (A : CompleteLocalSAlgebra S) :
    (A.residueOverHom).left = A.residueToSpec := sorry

/-- The complete local `Λ`-algebra structure of `A` with residue field `κ(A)`,
using the given `Λ`-algebra structure on the carrier of `A`. -/
def completeLocalAlgCat (A : CompleteLocalSAlgebra S) (Λ : Type u)
    [CommRing Λ] [IsNoetherianRing Λ] [Algebra Λ A.carrier]
    [Module.Finite Λ (ResidueField A.carrier)] :
    CompleteLocalAlgCat Λ (ResidueField A.carrier) :=
  CompleteLocalAlgCat.of A.carrier AlgEquiv.refl

/-- The complete local `Λ`-algebra of `A` has the same carrier as `A`. -/
theorem completeLocalAlgCat_carrier (A : CompleteLocalSAlgebra S) (Λ : Type u)
    [CommRing Λ] [IsNoetherianRing Λ] [Algebra Λ A.carrier]
    [Module.Finite Λ (ResidueField A.carrier)] :
    (A.completeLocalAlgCat Λ).carrier = A.carrier := sorry

/-- The first truncation of `A` is the residue-field spectrum of `A` over `S`. -/
theorem stageOver_zero_eq (A : CompleteLocalSAlgebra S) :
    A.stageOver 0 = Over.mk A.residueToS := sorry

/-- The morphism `Spec(k) ⟶ Spec(κ(A))` in `Over S` induced by a residue-field
identification compatible with the structure morphisms to `S`. -/
def residueStageHom {A : CompleteLocalSAlgebra S} {k : Type u} [Field k]
    {σ : Spec (CommRingCat.of k) ⟶ S} (e : ResidueField A.carrier ≃+* k)
    (h : residueSpecMap e ≫ A.toS = σ) :
    Over.mk σ ⟶ Over.mk A.residueToS :=
  Over.homMk (Spec.map (CommRingCat.ofHom e.toRingHom)) sorry

/-- `residueStageHom` is `Spec` of the residue-field identification. -/
theorem residueStageHom_left {A : CompleteLocalSAlgebra S} {k : Type u} [Field k]
    {σ : Spec (CommRingCat.of k) ⟶ S} (e : ResidueField A.carrier ≃+* k)
    (h : residueSpecMap e ≫ A.toS = σ) :
    (residueStageHom e h).left = Spec.map (CommRingCat.ofHom e.toRingHom) := sorry

end AlgebraicGeometry.CompleteLocalSAlgebra

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack is locally of finite type over a locally Noetherian scheme
`S` when it admits a surjective smooth atlas from a scheme locally of finite
type over `S`. -/
@[mk_iff]
class IsLocallyOfFiniteType {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : Prop where
  /-- There is a surjective smooth 1-morphism from the slice of a scheme
  locally of finite type over `S`. -/
  exists_locallyOfFiniteType_smooth_cover :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        AlgebraicGeometry.LocallyOfFiniteType U.hom

namespace IsLocallyOfFiniteType

/-- A locally of finite type algebraic stack admits a surjective smooth atlas
from a scheme locally of finite type over `S`. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsLocallyOfFiniteType X] :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        AlgebraicGeometry.LocallyOfFiniteType U.hom := sorry

/-- A surjective smooth atlas from a scheme locally of finite type over `S`
witnesses that the algebraic stack is locally of finite type over `S`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [AlgebraicGeometry.LocallyOfFiniteType U.hom] :
    IsLocallyOfFiniteType X := sorry

/-- An algebraic stack is locally of finite type over `S` if and only if it
admits a surjective smooth atlas from a scheme locally of finite type over
`S`. -/
theorem iff {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    IsLocallyOfFiniteType X ↔
      ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
          AlgebraicGeometry.LocallyOfFiniteType U.hom := sorry

end IsLocallyOfFiniteType

/-- The canonical slice of a scheme locally of finite type over `S` is a
locally of finite type algebraic stack. -/
instance instIsLocallyOfFiniteType_slice {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.LocallyOfFiniteType U.hom] :
    IsLocallyOfFiniteType (GroupoidsOver.slice U) where
  exists_locallyOfFiniteType_smooth_cover :=
    ⟨U, 𝟙 (GroupoidsOver.slice U), inferInstance, inferInstance, inferInstance⟩

/-- Locally of finite type over `S` is equivalent to locally of finite type of
the structure morphism to the identity fibration of `Over S`. -/
theorem isLocallyOfFiniteType_iff_baseProjection {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    IsLocallyOfFiniteType X ↔
      LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X) := sorry

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

/-- The identity object of the slice of `Spec(A)` as a complete local object. -/
def CompleteLocalObject.identity (A : CompleteLocalSAlgebra S) :
    CompleteLocalObject (slice (Over.mk A.toS)) :=
  CompleteLocalObject.of A (sliceIdentityObject A.toS)
    (sliceIdentityObject_over A.toS)

/-- The identity complete local object has base `A`. -/
theorem CompleteLocalObject.identity_base (A : CompleteLocalSAlgebra S) :
    (CompleteLocalObject.identity A).base = A := sorry

/-- The identity complete local object is the identity slice object over
`Spec(A)`. -/
theorem CompleteLocalObject.identity_spec (A : CompleteLocalSAlgebra S) :
    (CompleteLocalObject.identity A).object = sliceIdentityObject A.toS ∧
      (slice (Over.mk A.toS)).p.obj (CompleteLocalObject.identity A).object =
        Over.mk A.toS := sorry

namespace FormalObject

/-- The identity formal object of the slice of `Spec(A)`, obtained by
restricting the identity slice object along all truncations. -/
def identity (A : CompleteLocalSAlgebra S) :
    FormalObject (slice (Over.mk A.toS)) :=
  restriction (CompleteLocalObject.identity A)

/-- The identity formal object has complete local base `A`. -/
theorem identity_base (A : CompleteLocalSAlgebra S) :
    (identity A).base = A := sorry

/-- The identity formal object is the truncation system of the identity slice
object of `Spec(A)`. -/
theorem identity_spec (A : CompleteLocalSAlgebra S) :
    (identity A).base = A ∧
      (identity A).stageOne =
        restrictionObj (CompleteLocalObject.identity A) 0 := sorry

/-- The first stage of a formal object lies over `Spec(κ(A)) ⟶ S`. -/
theorem stageOne_eq_residueOver {X : GroupoidsOver S} (ξ : FormalObject X) :
    X.p.obj ξ.stageOne = Over.mk ξ.base.residueToS := sorry

/-- The first stage of `ξ` as an object of the fibre over `Spec(κ(A)) ⟶ S`. -/
def stageOneFiber {X : GroupoidsOver S} (ξ : FormalObject X) :
    X.p.Fiber (Over.mk ξ.base.residueToS) :=
  Functor.Fiber.mk (stageOne_eq_residueOver ξ)

/-- `stageOneFiber ξ` is `ξ.stageOne` in the residue fibre of `ξ.base`. -/
theorem stageOneFiber_spec {X : GroupoidsOver S} (ξ : FormalObject X) :
    Functor.Fiber.fiberInclusion.obj (stageOneFiber ξ) = ξ.stageOne := sorry

/-- A based functor from the restricted coyoneda of the complete local base of
`ξ` represents `ξ` in the predeformation category of `ξ.stageOne` when it sends
identity truncations to the stages of `ξ`, following `FormalObject.Represents`. -/
def Represents {X : GroupoidsOver S} (ξ : FormalObject X)
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ ξ.base.carrier]
    [Module.Finite Λ (ResidueField ξ.base.carrier)]
    {openImmersion : Spec (CommRingCat.of Λ) ⟶ S}
    [IsOpenImmersion openImmersion]
    {h_factor :
      Spec.map (CommRingCat.ofHom
          (algebraMap Λ (ResidueField ξ.base.carrier))) ≫
        openImmersion =
      ξ.base.residueToS}
    (φ : BasedCategory.ofFunctor
        (CompleteLocalAlgCat.identityProjection (ξ.base.completeLocalAlgCat Λ)) ⥤ᵇ
      Predeformation.predeformation openImmersion h_factor X (stageOneFiber ξ)) :
    Prop :=
  ∃ h : ∀ n,
      Functor.Fiber.fiberInclusion.obj
          (φ.obj
            (CompleteLocalAlgCat.identityStage (ξ.base.completeLocalAlgCat Λ) n)).target =
        ξ.objects n,
    ∀ n,
      (φ.map
          (CompleteLocalAlgCat.identityStageMap (ξ.base.completeLocalAlgCat Λ) n)).hom =
        eqToHom (h n) ≫ ξ.step n ≫ eqToHom (h (n + 1)).symm

/-- A representing based functor sends identity truncations to the stages of
`ξ`. -/
theorem represents_obj {X : GroupoidsOver S} (ξ : FormalObject X)
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ ξ.base.carrier]
    [Module.Finite Λ (ResidueField ξ.base.carrier)]
    {openImmersion : Spec (CommRingCat.of Λ) ⟶ S}
    [IsOpenImmersion openImmersion]
    {h_factor :
      Spec.map (CommRingCat.ofHom
          (algebraMap Λ (ResidueField ξ.base.carrier))) ≫
        openImmersion =
      ξ.base.residueToS}
    (φ : BasedCategory.ofFunctor
        (CompleteLocalAlgCat.identityProjection (ξ.base.completeLocalAlgCat Λ)) ⥤ᵇ
      Predeformation.predeformation openImmersion h_factor X (stageOneFiber ξ))
    (hφ : Represents ξ φ) (n : ℕ) :
    Functor.Fiber.fiberInclusion.obj
        (φ.obj
          (CompleteLocalAlgCat.identityStage (ξ.base.completeLocalAlgCat Λ) n)).target =
      ξ.objects n := sorry

/-- A formal object of a category fibred in groupoids over `(Sch/S)_fppf` is
versal when, after every affine-open factorization of its residue point, it is
represented by a smooth morphism of predeformation categories from the
restricted coyoneda of its complete local base. -/
class IsVersal {X : GroupoidsOver S} (ξ : FormalObject X) : Prop where
  /-- Smooth based functor representing `ξ` in the predeformation category of
  `ξ.stageOne` after every affine-open factorization of the residue point. -/
  exists_smooth_representation :
    ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
      [Algebra Λ ξ.base.carrier]
      [Module.Finite Λ (ResidueField ξ.base.carrier)]
      (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
      [IsOpenImmersion openImmersion]
      (h_factor :
        Spec.map (CommRingCat.ofHom
            (algebraMap Λ (ResidueField ξ.base.carrier))) ≫
          openImmersion =
        ξ.base.residueToS),
      ∃ φ : BasedCategory.ofFunctor
          (CompleteLocalAlgCat.identityProjection (ξ.base.completeLocalAlgCat Λ)) ⥤ᵇ
        Predeformation.predeformation openImmersion h_factor X (stageOneFiber ξ),
        Represents ξ φ ∧ BasedFunctor.IsSmooth φ

namespace IsVersal

/-- Versality supplies a smooth based functor representing `ξ` in the
predeformation category of `ξ.stageOne` after every affine-open factorization
of the residue point. -/
theorem spec {X : GroupoidsOver S} (ξ : FormalObject X) [IsVersal ξ]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ ξ.base.carrier]
    [Module.Finite Λ (ResidueField ξ.base.carrier)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom
          (algebraMap Λ (ResidueField ξ.base.carrier))) ≫
        openImmersion =
      ξ.base.residueToS) :
    ∃ φ : BasedCategory.ofFunctor
        (CompleteLocalAlgCat.identityProjection (ξ.base.completeLocalAlgCat Λ)) ⥤ᵇ
      Predeformation.predeformation openImmersion h_factor X (stageOneFiber ξ),
      Represents ξ φ ∧ BasedFunctor.IsSmooth φ := sorry

/-- Versality is the existence of a smooth based functor representing `ξ` in the
predeformation category of `ξ.stageOne` after every affine-open factorization
of the residue point. -/
theorem iff {X : GroupoidsOver S} (ξ : FormalObject X) :
    IsVersal ξ ↔
      ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
        [Algebra Λ ξ.base.carrier]
        [Module.Finite Λ (ResidueField ξ.base.carrier)]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [IsOpenImmersion openImmersion]
        (h_factor :
          Spec.map (CommRingCat.ofHom
              (algebraMap Λ (ResidueField ξ.base.carrier))) ≫
            openImmersion =
          ξ.base.residueToS),
        ∃ φ : BasedCategory.ofFunctor
            (CompleteLocalAlgCat.identityProjection (ξ.base.completeLocalAlgCat Λ)) ⥤ᵇ
          Predeformation.predeformation openImmersion h_factor X (stageOneFiber ξ),
          Represents ξ φ ∧ BasedFunctor.IsSmooth φ := sorry

end IsVersal

/-- The identity formal object of the slice of `Spec(A)` is versal. -/
instance instIsVersal_identity (A : CompleteLocalSAlgebra S) :
    IsVersal (identity A) := sorry

end FormalObject

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

/-- The residue-field point of the slice of `Spec(A)`. -/
def residueFieldValuedPoint (A : CompleteLocalSAlgebra S) :
    FieldValuedPoint (GroupoidsOver.slice (Over.mk A.toS)) :=
  FieldValuedPoint.of (ResidueField A.carrier) A.residueToS
    (overMap A.residueOverHom)

/-- The residue-field point of `A` has source field `κ(A)` and structure
morphism `A.residueToS`. -/
theorem residueFieldValuedPoint_spec (A : CompleteLocalSAlgebra S) :
    (residueFieldValuedPoint A).K = ResidueField A.carrier ∧
      (residueFieldValuedPoint A).structureHom = A.residueToS := sorry

/-- The first stage of a formal object is compatible with a field-valued point
when the residue field of the complete local base is identified with the source
field over `S` and the corresponding objects of `X` are isomorphic over that
residue identification. -/
def StageOneCompatible {X : GroupoidsOver S} (x0 : FieldValuedPoint X)
    (ξ : GroupoidsOver.FormalObject X) : Prop :=
  ∃ (e : ResidueField ξ.base.carrier ≃+* x0.K)
    (h : residueSpecMap e ≫ ξ.base.toS = x0.structureHom)
    (α : (toFunctor x0.hom).obj (GroupoidsOver.sliceIdentityObject x0.structureHom) ≅
      ξ.stageOne),
    X.p.IsHomLift
      (CompleteLocalSAlgebra.residueStageHom e h ≫
        eqToHom (CompleteLocalSAlgebra.stageOver_zero_eq ξ.base).symm)
      α.hom

/-- Stage-one compatibility unpacks to a residue-field identification over `S`
together with an isomorphism of objects of `X` lying over that identification. -/
theorem stageOneCompatible_iff {X : GroupoidsOver S} (x0 : FieldValuedPoint X)
    (ξ : GroupoidsOver.FormalObject X) :
    StageOneCompatible x0 ξ ↔
      ∃ (e : ResidueField ξ.base.carrier ≃+* x0.K)
        (h : residueSpecMap e ≫ ξ.base.toS = x0.structureHom)
        (α : (toFunctor x0.hom).obj
            (GroupoidsOver.sliceIdentityObject x0.structureHom) ≅ ξ.stageOne),
        X.p.IsHomLift
          (CompleteLocalSAlgebra.residueStageHom e h ≫
            eqToHom (CompleteLocalSAlgebra.stageOver_zero_eq ξ.base).symm)
          α.hom := sorry

/-- A complete local `S`-algebra `A` is a versal ring to `X` at a finite type
field-valued point `x0` when its residue field is identified with the source
field of `x0` over `S` and it carries a versal formal object of `X` whose first
stage is 2-isomorphic to `x0`. -/
class IsVersalRing {X : GroupoidsOver S} [AlgebraicStack X]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) : Prop where
  /-- Residue field of `A` identified with the source field of `x0` over `S`. -/
  residue_iso :
    ∃ e : ResidueField A.carrier ≃+* x0.K,
      residueSpecMap e ≫ A.toS = x0.structureHom
  /-- There is a versal formal object of `X` on `A` with first stage
  2-isomorphic to `x0`. -/
  exists_versal_formalObject :
    ∃ ξ : GroupoidsOver.FormalObject X,
      ξ.base = A ∧ StageOneCompatible x0 ξ ∧ GroupoidsOver.FormalObject.IsVersal ξ

namespace IsVersalRing

/-- A versal ring supplies a residue identification and a versal formal object
compatible with `x0`. -/
theorem spec {X : GroupoidsOver S} [AlgebraicStack X]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A] :
    (∃ e : ResidueField A.carrier ≃+* x0.K,
        residueSpecMap e ≫ A.toS = x0.structureHom) ∧
      ∃ ξ : GroupoidsOver.FormalObject X,
        ξ.base = A ∧ StageOneCompatible x0 ξ ∧ GroupoidsOver.FormalObject.IsVersal ξ :=
  sorry

/-- Being a versal ring is a residue identification together with a versal
formal object on `A` compatible with `x0`. -/
theorem iff {X : GroupoidsOver S} [AlgebraicStack X]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) :
    IsVersalRing x0 A ↔
      (∃ e : ResidueField A.carrier ≃+* x0.K,
          residueSpecMap e ≫ A.toS = x0.structureHom) ∧
        ∃ ξ : GroupoidsOver.FormalObject X,
          ξ.base = A ∧ StageOneCompatible x0 ξ ∧ GroupoidsOver.FormalObject.IsVersal ξ :=
  sorry

end IsVersalRing

/-- The residue-field point of `A` is locally of finite type over `S`. -/
instance instLocallyOfFiniteType_residueFieldValuedPoint (A : CompleteLocalSAlgebra S) :
    AlgebraicGeometry.LocallyOfFiniteType (residueFieldValuedPoint A).structureHom :=
  A.residue_locallyOfFiniteType

/-- A complete local `S`-algebra is a versal ring to the slice of its spectrum
at the residue-field point. -/
instance instIsVersalRing_residueFieldValuedPoint (A : CompleteLocalSAlgebra S) :
    IsVersalRing (residueFieldValuedPoint A) A := sorry

end AlgebraicGeometry.AlgebraicStack
