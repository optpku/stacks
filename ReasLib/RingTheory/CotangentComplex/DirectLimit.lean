module

public import ReasLib.RingTheory.CotangentComplex.Functoriality
public import ReasLib.RingTheory.DirectLimit.Algebra
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Directed limits of cotangent complexes

The degreewise direct limit of scalar-extended stage complexes carries a
canonical comparison to the cotangent complex of the induced map of ring direct limits.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicTopology
open HomologicalComplex
open scoped Simplicial ZeroObject

universe u

noncomputable section

namespace Algebra.CotangentComplex.DirectLimit

variable {I : Type u} [Preorder I]
variable {R S : I → Type u}
variable [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]
variable (ρ : ∀ i j, i ≤ j → R i →+* R j)
variable (σ : ∀ i j, i ≤ j → S i →+* S j)

/-- The ring homomorphism induced on direct limits by a compatible family of stage maps. -/
@[stacks 08S9]
noncomputable abbrev limitHom
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    Ring.DirectLimit R (fun i j h ↦ ρ i j h) →+*
      Ring.DirectLimit S (fun i j h ↦ σ i j h) :=
  Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h

/-- Unfolding of `limitHom` as `Ring.DirectLimit.map` of the stage algebra maps. -/
@[stacks 08S9]
theorem limitHom_eq
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    limitHom ρ σ hcomm =
      Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h :=
  rfl

/-- The André-Quillen cotangent complex of the induced direct-limit algebra map. -/
@[stacks 08S9]
noncomputable def targetComplex
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    CochainComplex (ModuleCat.{u} (Ring.DirectLimit S (fun i j h ↦ σ i j h))) ℤ :=
  RingHom.cotangentComplex (limitHom ρ σ hcomm)

/-- Unfolding of `targetComplex` as the cotangent complex of `limitHom`. -/
@[stacks 08S9]
theorem targetComplex_eq
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    targetComplex ρ σ hcomm = RingHom.cotangentComplex (limitHom ρ σ hcomm) :=
  rfl

namespace Stage

/-- The André-Quillen cotangent complex at a stage, extended to the common target
direct-limit ring. -/
@[stacks 08S9]
noncomputable def complex (i : I) :
    CochainComplex (ModuleCat.{u} (Ring.DirectLimit S (fun i j h ↦ σ i j h))) ℤ :=
  ((ModuleCat.extendScalars (Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
    (Algebra.cotangentComplex (R i) (S i))

/-- The degree-`n` module in the common-target cotangent complex of a stage. -/
@[stacks 08S9]
noncomputable abbrev component (n : ℤ) (i : I) :
    ModuleCat.{u} (Ring.DirectLimit S (fun i j h ↦ σ i j h)) :=
  (complex (R := R) (S := S) (σ := σ) i).X n

/-- The two scalar-extension routes from a stage to the target direct limit give the
same source complex. -/
theorem complex_eq_extendScalars_comp {i j : I} (h : i ≤ j) :
    complex (R := R) (S := S) (σ := σ) i =
      ((ModuleCat.extendScalars
          ((Ring.DirectLimit.of S (fun i j h ↦ σ i j h) j).comp (σ i j h))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (Algebra.cotangentComplex (R i) (S i)) :=
  sorry

/-- The canonical map from a stage cotangent complex after extending scalars to a
later stage, induced by the transition square. -/
@[stacks 08S9]
noncomputable def transition
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    complex (R := R) (S := S) (σ := σ) i ⟶ complex (R := R) (S := S) (σ := σ) j :=
  let C := Algebra.cotangentComplex (R i) (S i)
  let sigmaIJ : S i →+* S j := σ i j h
  let sigmaJTarget : S j →+* Ring.DirectLimit S (fun i j h ↦ σ i j h) :=
    Ring.DirectLimit.of S (fun i j h ↦ σ i j h) j
  eqToHom
      (congrArg
        (fun φ : S i →+* Ring.DirectLimit S (fun i j h ↦ σ i j h) =>
          ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
        (RingHom.ext fun x =>
          (Ring.DirectLimit.of_f
            (f := fun i j hij => (σ i j hij : S i → S j)) h x).symm)) ≫
    (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp sigmaIJ sigmaJTarget)
        (ComplexShape.up ℤ)).hom.app C ≫
      ((ModuleCat.extendScalars sigmaJTarget).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Algebra.CotangentComplex.map (algebraMap (R i) (S i)) (algebraMap (R j) (S j))
          (ρ i j h) (σ i j h) (hcomm h))

/-- The canonical map from a stage complex to the cotangent complex of the
direct-limit algebra map. -/
@[stacks 08S9]
noncomputable def toTarget
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    complex (R := R) (S := S) (σ := σ) i ⟶ targetComplex ρ σ hcomm :=
  Algebra.CotangentComplex.map (algebraMap (R i) (S i)) (limitHom ρ σ hcomm)
    (Ring.DirectLimit.of R (fun i j h ↦ ρ i j h) i)
    (Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i)
    (Ring.DirectLimit.Algebra.map_comp_of (ρ := ρ) (σ := σ)
      (fun k ↦ algebraMap (R k) (S k)) hcomm i)

/-- The degree-`n` linear transition map between common-target stage components. -/
@[stacks 08S9]
noncomputable abbrev componentMap
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (n : ℤ) {i j : I} (h : i ≤ j) :
    component (R := R) (S := S) (σ := σ) n i →ₗ[Ring.DirectLimit S (fun i j h ↦ σ i j h)]
      component (R := R) (S := S) (σ := σ) n j :=
  ((transition ρ σ hcomm h).f n).hom

/-- The stage transition along an identity index relation is the identity chain map. -/
@[stacks 08S9]
theorem transition_id
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    transition ρ σ hcomm (le_rfl : i ≤ i) = 𝟙 _ :=
  sorry

/-- Stage transitions compose along composable index relations. -/
@[stacks 08S9]
theorem transition_comp
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    transition ρ σ hcomm hij ≫ transition ρ σ hcomm hjk =
      transition ρ σ hcomm (hij.trans hjk) :=
  sorry

/-- The maps from stages to the target direct-limit complex form a compatible
cocone over the stage transitions. -/
@[stacks 08S9]
theorem toTarget_comp_transition
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    transition ρ σ hcomm h ≫ toTarget ρ σ hcomm j = toTarget ρ σ hcomm i :=
  sorry

/-- The degree-`n` components of the canonical stage complexes form a directed
system whenever the base and target ring systems do. -/
@[stacks 08S9, instance]
theorem componentDirectedSystem
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (n : ℤ) :
    DirectedSystem
      (fun i ↦ (component (R := R) (S := S) (σ := σ) n i : Type u))
      (fun {_ _} h x ↦ componentMap ρ σ hcomm n h x) :=
  sorry

/-- Stage differentials commute with the common-target stage transitions. -/
theorem differentialCompatible
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (n m : ℤ) {i j : I} (h : i ≤ j) :
    ((complex (R := R) (S := S) (σ := σ) j).d n m).hom ∘ₗ
        ((transition ρ σ hcomm h).f n).hom =
      ((transition ρ σ hcomm h).f m).hom ∘ₗ
        ((complex (R := R) (S := S) (σ := σ) i).d n m).hom :=
  sorry

/-- The degree-`n` components of the stage-to-target maps are compatible with
stage transitions. -/
theorem toTarget_component_compatible
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (n : ℤ) {i j : I} (h : i ≤ j)
    (x : component (R := R) (S := S) (σ := σ) n i) :
    ((toTarget ρ σ hcomm j).f n).hom (((transition ρ σ hcomm h).f n).hom x) =
      ((toTarget ρ σ hcomm i).f n).hom x :=
  sorry

end Stage

namespace Model

/-- The degree-`n` module of the direct-limit model. -/
@[stacks 08S9]
noncomputable abbrev component
    (n : ℤ)
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    ModuleCat.{u} (Ring.DirectLimit S (fun i j h ↦ σ i j h)) :=
  -- Local instance justification (defeq pin): `Module.DirectLimit` requires `DecidableEq I`; pin `Classical.decEq` so every degree uses the same instance.
  letI : DecidableEq I := Classical.decEq I
  ModuleCat.of (Ring.DirectLimit S (fun i j h ↦ σ i j h)) <|
    Module.DirectLimit
      (fun i ↦ (Stage.complex (R := R) (S := S) (σ := σ) i).X n)
      (fun _ _ h ↦ ((Stage.transition ρ σ hcomm h).f n).hom)

/-- The differential on the degreewise direct limit is induced by the stage differentials. -/
noncomputable def differential
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (n m : ℤ) :
    component ρ σ n hcomm ⟶ component ρ σ m hcomm :=
  -- Local instance justification (defeq pin): `Module.DirectLimit` requires `DecidableEq I`; pin `Classical.decEq` so every degree uses the same instance.
  letI : DecidableEq I := Classical.decEq I
  ModuleCat.ofHom <|
    Module.DirectLimit.map
      (fun i ↦ ((Stage.complex (R := R) (S := S) (σ := σ) i).d n m).hom)
      (fun _ _ h => Stage.differentialCompatible ρ σ hcomm n m h)

/-- The induced differential vanishes outside the cochain complex shape. -/
theorem differential_shape
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (n m : ℤ) (h : ¬ (ComplexShape.up ℤ).Rel n m) :
    differential ρ σ hcomm n m = 0 :=
  sorry

/-- The direct-limit cochain complex formed from the stagewise cotangent complexes
after extending scalars to the target direct limit. -/
@[stacks 08S9]
noncomputable def complex
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    CochainComplex (ModuleCat.{u} (Ring.DirectLimit S (fun i j h ↦ σ i j h))) ℤ where
  X n := component ρ σ n hcomm
  d n m := differential ρ σ hcomm n m
  shape := differential_shape ρ σ hcomm
  d_comp_d' := sorry

/-- The degree-`n` object of the direct-limit model is the corresponding component. -/
theorem complex_X
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (n : ℤ) :
    (complex ρ σ hcomm).X n = component ρ σ n hcomm :=
  rfl

end Model

/-- The canonical comparison from the direct-limit model of the stagewise cotangent
complexes to the cotangent complex of the direct-limit algebra map. -/
@[stacks 08S9]
noncomputable def comparison
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    Model.complex ρ σ hcomm ⟶ targetComplex ρ σ hcomm where
  f n :=
    -- Local instance justification (defeq pin): `Module.DirectLimit` requires `DecidableEq I`; pin `Classical.decEq` so every degree uses the same instance.
    letI : DecidableEq I := Classical.decEq I
    ModuleCat.ofHom <|
      Module.DirectLimit.lift
        (Ring.DirectLimit S (fun i j h ↦ σ i j h)) I
        (fun i ↦ (Stage.complex (R := R) (S := S) (σ := σ) i).X n)
        (fun _ _ h ↦ ((Stage.transition ρ σ hcomm h).f n).hom)
        (fun i ↦ ((Stage.toTarget ρ σ hcomm i).f n).hom)
        (fun _ _ h x => Stage.toTarget_component_compatible ρ σ hcomm n h x)
  comm' := sorry

/-- Chain-map commutativity for the canonical direct-limit comparison. -/
theorem comparison_comm
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (n m : ℤ) :
    (Model.complex ρ σ hcomm).d n m ≫ (comparison ρ σ hcomm).f m =
      (comparison ρ σ hcomm).f n ≫ (targetComplex ρ σ hcomm).d n m :=
  (comparison ρ σ hcomm).comm n m |>.symm

/-- The canonical comparison from the direct limit of scalar-extended cotangent
complexes to the cotangent complex of the induced direct-limit ring map is an
isomorphism for a nonempty directed system. -/
@[stacks 08S9, instance]
theorem comparison_isIso
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    {R S : I → Type u}
    [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]
    (ρ : ∀ i j, i ≤ j → R i →+* R j)
    (σ : ∀ i j, i ≤ j → S i →+* S j)
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    IsIso (comparison ρ σ hcomm) :=
  sorry

end Algebra.CotangentComplex.DirectLimit
