/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.ExtendScalars
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Canonical
public import ReasLib.RingTheory.DirectLimit.Algebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Directed limits of canonical naive cotangent complexes

@stack 07BQ

This leaf owns the canonical direct-limit model associated to a directed
system of commutative-ring maps `R i → S i`.  It uses `Ring.DirectLimit` and
`Module.DirectLimit` from mathlib; only the cotangent-specific stage maps and
comparison are defined here.  It follows the universe convention of the
presentation-level target-changing map used to construct its stage maps.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped NaiveCotangent

universe u

noncomputable section

namespace Algebra.NaiveCotangent.DirectLimit

variable {I : Type u} [Preorder I]
variable {R S : I → Type u}
variable [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]
variable {ρ : ∀ i j, i ≤ j → R i →+* R j}
variable {σ : ∀ i j, i ≤ j → S i →+* S j}

/- `Rlim` and `Slim` are local readability notation only.  The public API
uses `Ring.DirectLimit` and the neutral direct-limit algebra owner directly. -/
local notation "Rlim" => Ring.DirectLimit R (fun i j h ↦ ρ i j h)
local notation "Slim" => Ring.DirectLimit S (fun i j h ↦ σ i j h)

namespace Stage

/-- The canonical naive cotangent complex at a stage, extended to the common
target direct-limit ring. -/
@[stacks 07BQ "direct-limit naive cotangent stage"]
noncomputable def complex (i : I) :
    ChainComplex (ModuleCat.{u} Slim) ℕ :=
  -- Local declaration justification (definitional pin): this is the named stage-to-limit
  -- algebra structure; registering it globally would compete with other ambient actions.
  letI : Algebra (S i) Slim :=
    Ring.DirectLimit.Algebra.stageAlgebra (fun i j h ↦ σ i j h) i
  Extension.NaiveCotangent.ExtendScalars.source
    ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension)

end Stage

/-- The ring homomorphism induced on direct limits by a compatible family of stage maps. -/
@[stacks 07BQ "direct-limit algebra map"]
noncomputable abbrev limitHom
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    Rlim →+* Slim :=
  Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h

/-- The canonical naive cotangent complex of the direct-limit algebra map. -/
@[stacks 07BQ "direct-limit naive cotangent target"]
noncomputable def targetComplex
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    ChainComplex (ModuleCat.{u} Slim) ℕ :=
  RingHom.naiveCotangent (limitHom (ρ := ρ) (σ := σ) hcomm)

namespace Stage

/-- The canonical map from a stage naive cotangent complex after extending
scalars to a later stage, induced by the transition square of presentations. -/
@[stacks 07BQ "direct-limit naive cotangent stage transition"]
noncomputable def transitionBase
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    (((ModuleCat.extendScalars (σ i j h)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Extension.NaiveCotangent.complex
        ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension))) ⟶
      Extension.NaiveCotangent.complex
        ((Generators.self (R j) (S j) : Generators (R j) (S j) (S j)).toExtension) :=
  -- Local declaration justification (transition square): these actions are selected by `ρ`,
  -- `σ`, and `hcomm`, so they are not canonical global instances for the four rings.
  letI : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  letI : Algebra (S i) (S j) := (σ i j h).toAlgebra
  letI : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  letI : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  Extension.NaiveCotangent.ExtendScalars.map (Generators.defaultHom Pi Pj).toExtensionHom

/-- The canonical map from a stage complex to the naive cotangent complex of
the direct-limit algebra map. -/
@[stacks 07BQ "direct-limit naive cotangent stage comparison"]
noncomputable def toTarget
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    complex (R := R) (S := S) (σ := σ) i ⟶ targetComplex (ρ := ρ) (σ := σ) hcomm :=
  -- Local declaration justification (comparison square): the chosen direct-limit map fixes
  -- these algebra and scalar-tower structures; global registration would create diamonds.
  letI : Algebra (R i) Rlim :=
    Ring.DirectLimit.Algebra.stageAlgebra (fun i j h ↦ ρ i j h) i
  letI : Algebra (S i) Slim :=
    Ring.DirectLimit.Algebra.stageAlgebra (fun i j h ↦ σ i j h) i
  letI : Algebra (R i) Slim :=
    ((limitHom (ρ := ρ) (σ := σ) hcomm).comp
      (Ring.DirectLimit.of R (fun i j h ↦ ρ i j h) i)).toAlgebra
  letI : Algebra Rlim Slim :=
    (limitHom (ρ := ρ) (σ := σ) hcomm).toAlgebra
  letI : IsScalarTower (R i) Rlim Slim :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (R i) (S i) Slim :=
    IsScalarTower.of_algebraMap_eq'
      (Ring.DirectLimit.Algebra.map_comp_of
        (ρ := ρ) (σ := σ) (fun k ↦ algebraMap (R k) (S k)) hcomm i)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let PInf : Generators Rlim Slim Slim := Generators.self Rlim Slim
  Extension.NaiveCotangent.ExtendScalars.map (Generators.defaultHom Pi PInf).toExtensionHom

/-- The two scalar-extension routes from a stage to the target direct limit
give the same source complex. -/
theorem transitionSource_eq
    {i j : I} (h : i ≤ j) :
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let C : ChainComplex (ModuleCat.{u} (S i)) ℕ :=
      Extension.NaiveCotangent.complex Pi.toExtension
    let sigmaIJ : S i →+* S j := σ i j h
    let sigmaJTarget : S j →+* Slim := Ring.DirectLimit.of S (fun i j h ↦ σ i j h) j
    ((ModuleCat.extendScalars (Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C =
      ((ModuleCat.extendScalars (sigmaJTarget.comp sigmaIJ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C := sorry

/-- The canonical transition between stage complexes after extending all
scalars to the common target direct-limit ring. -/
@[stacks 07BQ "direct-limit naive cotangent stage transition"]
noncomputable def transition
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    complex (R := R) (S := S) (σ := σ) i ⟶ complex (R := R) (S := S) (σ := σ) j :=
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let C : ChainComplex (ModuleCat.{u} (S i)) ℕ :=
    Extension.NaiveCotangent.complex Pi.toExtension
  let sigmaIJ : S i →+* S j := σ i j h
  let sigmaJTarget : S j →+* Slim := Ring.DirectLimit.of S (fun i j h ↦ σ i j h) j
  eqToHom (transitionSource_eq (σ := σ) h) ≫
    ((NatIso.mapHomologicalComplex
      (ModuleCat.extendScalarsComp sigmaIJ sigmaJTarget) (ComplexShape.down ℕ)).hom.app C) ≫
    ((ModuleCat.extendScalars sigmaJTarget).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (transitionBase (ρ := ρ) (σ := σ) hcomm h)

/-- The degree-`n` module in the common-target naive cotangent complex of a
stage. -/
@[stacks 07BQ "direct-limit naive cotangent stage component"]
noncomputable abbrev component (n : ℕ) (i : I) :
    ModuleCat.{u} Slim :=
  (complex (R := R) (S := S) (σ := σ) i).X n

/-- The degree-`n` linear transition map between common-target stage
components. -/
@[stacks 07BQ "direct-limit naive cotangent stage component"]
noncomputable abbrev componentMap
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (n : ℕ) {i j : I} (h : i ≤ j) :
    component (R := R) (S := S) (σ := σ) n i →ₗ[Slim]
      component (R := R) (S := S) (σ := σ) n j :=
  ((transition (ρ := ρ) (σ := σ) hcomm h).f n).hom

/-- The stage transition along an identity index relation is the identity
chain map. -/
@[stacks 07BQ "direct-limit naive cotangent stage transition"]
theorem transition_id
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    transition (ρ := ρ) (σ := σ) hcomm (le_rfl : i ≤ i) = 𝟙 _ := sorry

/-- Stage transitions compose along composable index relations. -/
@[stacks 07BQ "direct-limit naive cotangent stage transition"]
theorem transition_comp
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    transition (ρ := ρ) (σ := σ) hcomm hij ≫
        transition (ρ := ρ) (σ := σ) hcomm hjk =
      transition (ρ := ρ) (σ := σ) hcomm (hij.trans hjk) := sorry

/-- The maps from stages to the target direct-limit complex form a compatible
cocone over the stage transitions. -/
@[stacks 07BQ "direct-limit naive cotangent stage comparison"]
theorem toTarget_comp_transition
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    transition (ρ := ρ) (σ := σ) hcomm h ≫
        toTarget (ρ := ρ) (σ := σ) hcomm j =
      toTarget (ρ := ρ) (σ := σ) hcomm i := sorry

/-- The degree-`n` components of the canonical stage complexes form a
directed system whenever the base and target ring systems do. -/
@[stacks 07BQ "direct-limit stage component system", instance]
theorem componentDirectedSystem
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (n : ℕ) :
    DirectedSystem
      (fun i ↦ (component (R := R) (S := S) (σ := σ) n i : Type u))
      (fun {_ _} h x ↦ componentMap (ρ := ρ) (σ := σ) hcomm n h x) := sorry

end Stage

namespace Model

-- Local declaration justification (definitional pin): `Module.DirectLimit` uses a
-- `DecidableEq I`; pinning `Classical.decEq` keeps all components definitionally aligned.

/-- The degree-`n` module of the direct-limit model. -/
@[stacks 07BQ "direct-limit naive cotangent model component"]
noncomputable abbrev component
    (n : ℕ)
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    ModuleCat.{u} Slim :=
  letI : DecidableEq I := Classical.decEq I
  ModuleCat.of Slim <|
    Module.DirectLimit
      (fun i ↦ (Stage.complex (R := R) (S := S) (σ := σ) i).X n)
      (fun _ _ h ↦ ((Stage.transition (ρ := ρ) (σ := σ) hcomm h).f n).hom)

/-- The degree-zero module of the direct-limit model, formed from the
degree-zero components of the common-target stage complexes. -/
@[stacks 07BQ "direct-limit naive cotangent model"]
noncomputable def zero
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    ModuleCat.{u} Slim :=
  component (R := R) (S := S) (ρ := ρ) (σ := σ) 0 hcomm

/-- The degree-one module of the direct-limit model, formed from the
degree-one components of the common-target stage complexes. -/
@[stacks 07BQ "direct-limit naive cotangent model"]
noncomputable def one
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    ModuleCat.{u} Slim :=
  component (R := R) (S := S) (ρ := ρ) (σ := σ) 1 hcomm

/-- The stage differentials commute with the direct-limit stage transitions. -/
theorem differentialCompatible
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i j : I) (h : i ≤ j) :
    (((Stage.complex (R := R) (S := S) (σ := σ) j).d 1 0).hom) ∘ₗ
        ((Stage.transition (ρ := ρ) (σ := σ) hcomm h).f 1).hom =
      ((Stage.transition (ρ := ρ) (σ := σ) hcomm h).f 0).hom ∘ₗ
        (((Stage.complex (R := R) (S := S) (σ := σ) i).d 1 0).hom) := sorry

/-- The differential of the direct-limit two-term model. -/
@[stacks 07BQ "direct-limit naive cotangent model"]
noncomputable def differential
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    one (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm ⟶
      zero (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm :=
  letI : DecidableEq I := Classical.decEq I
  ModuleCat.ofHom <|
    Module.DirectLimit.map
      (fun i ↦ ((Stage.complex (R := R) (S := S) (σ := σ) i).d 1 0).hom)
      (fun i j h ↦ differentialCompatible (ρ := ρ) (σ := σ) hcomm i j h)

/-- The direct-limit two-term complex formed from the stagewise canonical
naive cotangent complexes after extending scalars to the target direct limit.
Without directed-system coherence this is a quotient model; the filtered
comparison theorem below imposes the needed coherence assumptions. -/
@[stacks 07BQ "direct-limit naive cotangent model"]
noncomputable def complex
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    ChainComplex (ModuleCat.{u} Slim) ℕ :=
  ChainComplex.mk'
    (zero (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm)
    (one (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm)
    (differential (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm)
    (fun {_ _} _ ↦ ⟨ModuleCat.of Slim PUnit, 0, zero_comp⟩)

end Model

namespace Comparison

-- Local declaration justification (definitional pin): the comparison components must use the
-- same classical equality decision as the corresponding `Model` direct-limit components.

/-- The degree-zero stage maps to the target complex are compatible with the
stage transitions. -/
theorem zeroCompatible
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j)
    (x : (Stage.complex (R := R) (S := S) (σ := σ) i).X 0) :
    ((Stage.toTarget (ρ := ρ) (σ := σ) hcomm j).f 0).hom
        (((Stage.transition (ρ := ρ) (σ := σ) hcomm h).f 0).hom x) =
      ((Stage.toTarget (ρ := ρ) (σ := σ) hcomm i).f 0).hom x := sorry

/-- The degree-one stage maps to the target complex are compatible with the
stage transitions. -/
theorem oneCompatible
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j)
    (x : (Stage.complex (R := R) (S := S) (σ := σ) i).X 1) :
    ((Stage.toTarget (ρ := ρ) (σ := σ) hcomm j).f 1).hom
        (((Stage.transition (ρ := ρ) (σ := σ) hcomm h).f 1).hom x) =
      ((Stage.toTarget (ρ := ρ) (σ := σ) hcomm i).f 1).hom x := sorry

/-- The degree-`n` component of the canonical direct-limit comparison. -/
@[stacks 07BQ "direct-limit comparison component"]
noncomputable def component
    (n : ℕ)
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (hcompat :
      ∀ ⦃i j : I⦄ (h : i ≤ j)
        (x : (Stage.complex (R := R) (S := S) (σ := σ) i).X n),
        ((Stage.toTarget (ρ := ρ) (σ := σ) hcomm j).f n).hom
            (((Stage.transition (ρ := ρ) (σ := σ) hcomm h).f n).hom x) =
          ((Stage.toTarget (ρ := ρ) (σ := σ) hcomm i).f n).hom x) :
    Model.component (R := R) (S := S) (ρ := ρ) (σ := σ) n hcomm ⟶
      (targetComplex (ρ := ρ) (σ := σ) hcomm).X n :=
  letI : DecidableEq I := Classical.decEq I
  ModuleCat.ofHom <|
    Module.DirectLimit.lift Slim I
      (fun i ↦ (Stage.complex (R := R) (S := S) (σ := σ) i).X n)
      (fun _ _ h ↦ ((Stage.transition (ρ := ρ) (σ := σ) hcomm h).f n).hom)
      (fun i ↦ ((Stage.toTarget (ρ := ρ) (σ := σ) hcomm i).f n).hom)
      (fun _ _ h x ↦ hcompat h x)

/-- The degree-zero component of the canonical direct-limit comparison. -/
@[stacks 07BQ "degree-zero direct-limit comparison component"]
noncomputable def zero
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    Model.zero (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm ⟶
      (targetComplex (ρ := ρ) (σ := σ) hcomm).X 0 :=
  component (R := R) (S := S) (ρ := ρ) (σ := σ) 0 hcomm
    (fun _ _ h x ↦ zeroCompatible (ρ := ρ) (σ := σ) hcomm h x)

/-- The degree-one component of the canonical direct-limit comparison. -/
@[stacks 07BQ "degree-one direct-limit comparison component"]
noncomputable def one
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    Model.one (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm ⟶
      (targetComplex (ρ := ρ) (σ := σ) hcomm).X 1 :=
  component (R := R) (S := S) (ρ := ρ) (σ := σ) 1 hcomm
    (fun _ _ h x ↦ oneCompatible (ρ := ρ) (σ := σ) hcomm h x)

/-- The degree-one and degree-zero comparison components commute with their
differentials. -/
theorem oneZeroComm
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    one (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm ≫
        (targetComplex (ρ := ρ) (σ := σ) hcomm).d 1 0 =
      (Model.complex (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm).d 1 0 ≫
        zero (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm := sorry

/-- The zero higher component satisfies the inductive chain-map compatibility
condition for the direct-limit comparison. -/
theorem succComm
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (n : ℕ)
    (p :
      Σ' (zero : (Model.complex (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm).X n ⟶
            (targetComplex (ρ := ρ) (σ := σ) hcomm).X n)
          (one : (Model.complex (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm).X (n + 1) ⟶
            (targetComplex (ρ := ρ) (σ := σ) hcomm).X (n + 1)),
        one ≫ (targetComplex (ρ := ρ) (σ := σ) hcomm).d (n + 1) n =
          (Model.complex (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm).d (n + 1) n ≫ zero) :
    (0 : (Model.complex (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm).X (n + 2) ⟶
        (targetComplex (ρ := ρ) (σ := σ) hcomm).X (n + 2)) ≫
        (targetComplex (ρ := ρ) (σ := σ) hcomm).d (n + 2) (n + 1) =
      (Model.complex (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm).d (n + 2) (n + 1) ≫
        p.2.1 := sorry

/-- The higher components of the canonical direct-limit comparison are
canonically zero. -/
@[stacks 07BQ "higher direct-limit comparison components"]
noncomputable def succ
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (n : ℕ)
    (p :
      Σ' (zero : (Model.complex (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm).X n ⟶
            (targetComplex (ρ := ρ) (σ := σ) hcomm).X n)
          (one : (Model.complex (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm).X (n + 1) ⟶
            (targetComplex (ρ := ρ) (σ := σ) hcomm).X (n + 1)),
        one ≫ (targetComplex (ρ := ρ) (σ := σ) hcomm).d (n + 1) n =
          (Model.complex (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm).d (n + 1) n ≫ zero) :
    Σ' two : (Model.complex (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm).X (n + 2) ⟶
          (targetComplex (ρ := ρ) (σ := σ) hcomm).X (n + 2),
      two ≫ (targetComplex (ρ := ρ) (σ := σ) hcomm).d (n + 2) (n + 1) =
        (Model.complex (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm).d (n + 2) (n + 1) ≫
          p.2.1 :=
  ⟨0, succComm (ρ := ρ) (σ := σ) hcomm n p⟩

end Comparison

/-- The canonical comparison from the direct-limit model of the stagewise
naive cotangent complexes to the naive cotangent complex of the direct-limit
algebra map. -/
@[stacks 07BQ "direct-limit naive cotangent comparison"]
noncomputable def comparison
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    Model.complex (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm ⟶
      targetComplex (ρ := ρ) (σ := σ) hcomm :=
  ChainComplex.mkHom _ _
    (Comparison.zero (ρ := ρ) (σ := σ) hcomm)
    (Comparison.one (ρ := ρ) (σ := σ) hcomm)
    (Comparison.oneZeroComm (ρ := ρ) (σ := σ) hcomm)
    (Comparison.succ (ρ := ρ) (σ := σ) hcomm)

/-- Lemma 10.134.9 (`07BQ`): the canonical comparison from the filtered
direct-limit model of the stagewise naive cotangent complexes to the naive
cotangent complex of the direct-limit algebra map is an isomorphism. -/
@[stacks 07BQ "naive cotangent direct-limit comparison", instance]
theorem comparison_isIso
    [Nonempty I] [IsDirectedOrder I]
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    IsIso (comparison (ρ := ρ) (σ := σ) hcomm) := sorry

/-- The canonical isomorphism from the direct-limit model to the naive cotangent complex of the
direct-limit algebra map. -/
@[stacks 07BQ "direct-limit naive cotangent isomorphism"]
noncomputable def comparisonIso
    [Nonempty I] [IsDirectedOrder I]
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    Model.complex (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm ≅
      targetComplex (ρ := ρ) (σ := σ) hcomm :=
  asIso (comparison (ρ := ρ) (σ := σ) hcomm)

/-- The forward map of `comparisonIso` is the canonical direct-limit comparison. -/
@[simp, stacks 07BQ "direct-limit comparison isomorphism forward map"]
theorem comparisonIso_hom
    [Nonempty I] [IsDirectedOrder I]
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    (comparisonIso (ρ := ρ) (σ := σ) hcomm).hom =
      comparison (ρ := ρ) (σ := σ) hcomm := sorry

/-- The inverse map of `comparisonIso` is the categorical inverse of the canonical comparison. -/
@[simp, stacks 07BQ "direct-limit comparison isomorphism inverse map"]
theorem comparisonIso_inv
    [Nonempty I] [IsDirectedOrder I]
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    (comparisonIso (ρ := ρ) (σ := σ) hcomm).inv =
      inv (comparison (ρ := ρ) (σ := σ) hcomm) := sorry

/-- The first cotangent homology of the direct-limit algebra map, with its
canonical algebra structure kept internal to this owner. -/
@[stacks 07BQ "direct-limit cotangent H1"]
noncomputable abbrev h1Cotangent
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) : Type u :=
  @Algebra.H1Cotangent Rlim Slim _ _
    (limitHom (ρ := ρ) (σ := σ) hcomm).toAlgebra

namespace H1

/-- Injectivity of the stagewise degree-`1 → 0` differentials implies
subsingleton first cotangent homology once the degree-zero component diagram
and the direct-limit comparison are available. -/
@[stacks 07BQ "direct-limit cotangent H1"]
theorem subsingleton_of_injective
    [Nonempty I] [IsDirectedOrder I]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    [DirectedSystem
      (fun i ↦
        (Stage.component (R := R) (S := S) (σ := σ) 0 i : Type u))
      (fun {_ _} h x ↦ Stage.componentMap (ρ := ρ) (σ := σ) hcomm 0 h x)]
    [IsIso (comparison (ρ := ρ) (σ := σ) hcomm)]
    (hstage : ∀ i : I,
      Function.Injective (((Stage.complex (R := R) (S := S) (σ := σ) i).d 1 0).hom)) :
    Subsingleton (h1Cotangent (ρ := ρ) (σ := σ) hcomm) := sorry

/-- Stagewise injectivity of the degree-`1 → 0` differentials implies that
the first cotangent homology of the direct-limit algebra map is subsingleton. -/
@[stacks 07BQ "direct-limit cotangent H1"]
theorem subsingleton_of_stagewise_injective
    [Nonempty I] [IsDirectedOrder I]
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (hstage : ∀ i : I,
      Function.Injective (((Stage.complex (R := R) (S := S) (σ := σ) i).d 1 0).hom)) :
    Subsingleton (h1Cotangent (ρ := ρ) (σ := σ) hcomm) := sorry

end H1

end Algebra.NaiveCotangent.DirectLimit
