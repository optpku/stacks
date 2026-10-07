module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Kähler differentials and directed limits

@stack 031G

This file packages the direct-limit comparison for a compatible directed system
of commutative-ring maps.  The model is expressed in `ModuleCat` over the target
ring direct limit, so callers do not need to rebuild scalar-extension instances.
-/

@[expose] public section

open CategoryTheory
open Ring.DirectLimit

universe u

noncomputable section

namespace KaehlerDifferential.DirectLimit

variable {I : Type u} [Preorder I]
variable {R S : I → Type u}
variable [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]
variable {ρ : ∀ i j, i ≤ j → R i →+* R j}
variable {σ : ∀ i j, i ≤ j → S i →+* S j}

local notation "Rlim" => Ring.DirectLimit R (fun i j h ↦ ρ i j h)
local notation "Slim" => Ring.DirectLimit S (fun i j h ↦ σ i j h)

namespace Stage

/-- The ring map at a stage of the directed system. -/
@[stacks 031G]
abbrev hom (i : I) : CommRingCat.of (R i) ⟶ CommRingCat.of (S i) :=
  CommRingCat.ofHom (algebraMap (R i) (S i))

/-- The relative Kähler differential module at a stage. -/
@[stacks 031G]
abbrev differential (i : I) : ModuleCat (S i) :=
  CommRingCat.KaehlerDifferential (hom (R := R) (S := S) i)

/-- The canonical map from a target stage into its ring direct limit. -/
@[stacks 031G]
abbrev toLimit (i : I) : S i →+* Slim :=
  Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i

/-- The target direct-limit ring has its canonical algebra structure over every stage. -/
@[stacks 031G]
instance toLimitAlgebra (i : I) : Algebra (S i) Slim :=
  (toLimit (S := S) (σ := σ) i).toAlgebra

/-- The canonical map from a target stage into its direct limit as a categorical morphism. -/
@[stacks 031G]
abbrev toLimitHom (i : I) : CommRingCat.of (S i) ⟶ CommRingCat.of Slim :=
  CommRingCat.ofHom (toLimit (S := S) (σ := σ) i)

/-- The stage differential after scalar extension to the target ring direct limit. -/
@[stacks 031G]
noncomputable def baseChange (i : I) : ModuleCat Slim :=
  (ModuleCat.extendScalars (toLimitHom (S := S) (σ := σ) i).hom).obj
    (differential (R := R) (S := S) i)

/-- The scalar-extended stage differential carries the canonical module structure
over the target direct-limit ring.  This bridge makes that bundled structure
available to typeclass search through the opaque `ModuleCat` carrier. -/
@[stacks 031G]
instance baseChangeModule (i : I) :
    Module Slim (@baseChange I _ R S _ _ _ σ i) :=
  inferInstance

/-- The transition square in the directed system of ring maps. -/
@[stacks 031G]
theorem square
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    CommRingCat.ofHom (ρ i j h) ≫ hom (R := R) (S := S) j =
      hom (R := R) (S := S) i ≫ CommRingCat.ofHom (σ i j h) := sorry

/-- A compatible square of stage maps induces a map between the corresponding
Kähler differential modules after one scalar extension.  The algebra instance is
local because the transition map is not recoverable from its source and target alone. -/
@[stacks 031G]
noncomputable def transitionBase
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    (ModuleCat.extendScalars (σ i j h)).obj (differential (R := R) (S := S) i) ⟶
      differential (R := R) (S := S) j :=
  letI : Algebra (S i) (S j) := (σ i j h).toAlgebra
  ((ModuleCat.extendRestrictScalarsAdj (σ i j h)).homEquiv _ _).symm
    (CommRingCat.KaehlerDifferential.map (square (ρ := ρ) (σ := σ) hcomm h))

/-- The two maps from an earlier target stage to the direct limit agree. -/
@[stacks 031G]
theorem toLimit_comp {i j : I} (h : i ≤ j) :
    (toLimit (S := S) (σ := σ) j).comp (σ i j h) =
      toLimit (S := S) (σ := σ) i := sorry

/-- Scalar extension along the composite stage-to-limit map has the canonical
stage-base-change source. -/
@[stacks 031G]
theorem baseChange_eq_extendScalars_comp {i j : I} (h : i ≤ j) :
    baseChange (R := R) (S := S) (σ := σ) i =
      (ModuleCat.extendScalars
        ((toLimit (S := S) (σ := σ) j).comp (σ i j h))).obj
        (differential (R := R) (S := S) i) := sorry

/-- The transition between stage differentials after extending every stage to the
common target direct limit. -/
@[stacks 031G]
noncomputable def transition
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    baseChange (R := R) (S := S) (σ := σ) i ⟶
      baseChange (R := R) (S := S) (σ := σ) j :=
  eqToHom (baseChange_eq_extendScalars_comp (R := R) (S := S) (σ := σ) h) ≫
    (ModuleCat.extendScalarsComp (σ i j h)
      (toLimit (S := S) (σ := σ) j)).hom.app
      (differential (R := R) (S := S) i) ≫
      (ModuleCat.extendScalars (toLimit (S := S) (σ := σ) j)).map
        (transitionBase (ρ := ρ) (σ := σ) hcomm h)

end Stage

/-- The ring map induced by a compatible family of stage maps. -/
@[stacks 031G]
abbrev ringHom
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    Rlim →+* Slim :=
  Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h

/-- The Kähler differential module of the induced direct-limit ring map. -/
@[stacks 031G]
abbrev target
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    ModuleCat Slim :=
  CommRingCat.KaehlerDifferential (CommRingCat.ofHom (ringHom (ρ := ρ) (σ := σ) hcomm))

/-- The direct-limit differential has its canonical module structure over the
target direct-limit ring. -/
@[stacks 031G]
instance targetModule
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    Module Slim (@target I _ R S _ _ _ ρ σ hcomm) :=
  inferInstance

/-- The direct-limit square relating one stage to the induced map on direct limits. -/
@[stacks 031G]
theorem square
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    CommRingCat.ofHom (Ring.DirectLimit.of R (fun i j h ↦ ρ i j h) i) ≫
        CommRingCat.ofHom (ringHom (ρ := ρ) (σ := σ) hcomm) =
      Stage.hom (R := R) (S := S) i ≫
        CommRingCat.ofHom (Stage.toLimit (S := S) (σ := σ) i) := sorry

namespace Stage

/-- The canonical map from a base-changed stage differential to the differential
of the induced direct-limit ring map. -/
@[stacks 031G]
noncomputable def toTarget
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    baseChange (R := R) (S := S) (σ := σ) i ⟶ target (ρ := ρ) (σ := σ) hcomm :=
  ((ModuleCat.extendRestrictScalarsAdj (toLimit (S := S) (σ := σ) i)).homEquiv _ _).symm
    (CommRingCat.KaehlerDifferential.map
      (KaehlerDifferential.DirectLimit.square (ρ := ρ) (σ := σ) hcomm i))

/-- The stage-to-target maps form a cocone over the common-target stage transitions. -/
@[stacks 031G]
theorem toTarget_comp_transition
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    transition (ρ := ρ) (σ := σ) hcomm h ≫ toTarget (ρ := ρ) (σ := σ) hcomm j =
      toTarget (ρ := ρ) (σ := σ) hcomm i := sorry

end Stage

namespace Model

-- Local declaration justification (definitional pin): `Module.DirectLimit` requires a
-- `DecidableEq I`; all three constructors pin the same classical choice locally.

/-- The module direct limit of the base-changed stage differential modules. -/
@[stacks 031G]
noncomputable def module
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    ModuleCat Slim :=
  let _ : DecidableEq I := Classical.decEq I
  ModuleCat.of Slim <|
    Module.DirectLimit
      (fun i ↦ Stage.baseChange (R := R) (S := S) (σ := σ) i)
      (fun _ _ h ↦ (Stage.transition (ρ := ρ) (σ := σ) hcomm h).hom)

/-- The canonical map from a stage differential into the direct-limit model. -/
@[stacks 031G]
noncomputable def of
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    Stage.baseChange (R := R) (S := S) (σ := σ) i ⟶
      module (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm :=
  let _ : DecidableEq I := Classical.decEq I
  ModuleCat.ofHom
    (X := Stage.baseChange (R := R) (S := S) (σ := σ) i)
    (Y := module (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm) <|
    Module.DirectLimit.of Slim I
      (fun i ↦ Stage.baseChange (R := R) (S := S) (σ := σ) i)
      (fun _ _ h ↦ (Stage.transition (ρ := ρ) (σ := σ) hcomm h).hom) i

/-- A compatible family of maps out of stage differentials descends to the
direct-limit model. -/
@[stacks 031G]
noncomputable def desc
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {P : ModuleCat Slim}
    (g : ∀ i, Stage.baseChange (R := R) (S := S) (σ := σ) i ⟶ P)
    (hg : ∀ ⦃i j : I⦄ (h : i ≤ j),
      Stage.transition (ρ := ρ) (σ := σ) hcomm h ≫ g j = g i) :
    module (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm ⟶ P :=
  let _ : DecidableEq I := Classical.decEq I
  ModuleCat.ofHom
    (X := module (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm)
    (Y := P) <|
    Module.DirectLimit.lift Slim I
      (fun i ↦ Stage.baseChange (R := R) (S := S) (σ := σ) i)
      (fun _ _ h ↦ (Stage.transition (ρ := ρ) (σ := σ) hcomm h).hom)
      (fun i ↦ (g i).hom)
      (fun _ _ h x ↦ DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (hg h)) x)

end Model

/-- The canonical comparison from the direct limit of the base-changed stage
Kähler differentials to the Kähler differential of the direct-limit ring map. -/
@[stacks 031G]
noncomputable def comparison
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    Model.module (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm ⟶
      target (ρ := ρ) (σ := σ) hcomm :=
  Model.desc (R := R) (S := S) (ρ := ρ) (σ := σ) hcomm
    (fun i ↦ Stage.toTarget (ρ := ρ) (σ := σ) hcomm i)
    (fun _ _ h ↦ Stage.toTarget_comp_transition (ρ := ρ) (σ := σ) hcomm h)

/-- Lemma 10.131.5 (`031G`): for a directed system of commutative-ring maps,
the canonical comparison from the direct limit of the stagewise Kähler
differentials to the differential of the induced direct-limit map is an isomorphism. -/
@[stacks 031G]
theorem comparison_isIso
    [Nonempty I] [IsDirectedOrder I]
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    IsIso (comparison (ρ := ρ) (σ := σ) hcomm) := sorry

end KaehlerDifferential.DirectLimit
