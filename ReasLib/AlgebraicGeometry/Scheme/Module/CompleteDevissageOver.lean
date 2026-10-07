module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberMap
public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissageAt

/-!
# Complete dévissages over a point

This file packages the finite scheme-and-module diagram of a complete dévissage over a point of
the base scheme. The one-step conditions are kept as a predicate on explicit diagram data so
that successive cokernels can occur in a homogeneous finite family.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The explicit diagram data satisfy the conditions for a one-step dévissage of `F / X / S`
over `s`. -/
structure IsOneStepDevissageOver {S : Scheme.{u}} (X : Over S) (F : X.left.Modules) (s : S)
    (Z Y : Over S) (i : Z ⟶ X) (π : Z ⟶ Y) (G : Z.left.Modules) : Prop where
  /-- The structure morphism of the source is locally of finite type. -/
  locallyOfFiniteType : LocallyOfFiniteType X.hom
  /-- The source module is quasicoherent. -/
  sourceQuasicoherent : F.IsQuasicoherent
  /-- The source module is of finite type. -/
  sourceFiniteType : F.IsFiniteType
  /-- The base scheme is affine. -/
  isAffineS : IsAffine S
  /-- The source scheme is affine. -/
  isAffineX : IsAffine X.left
  /-- The scheme carrying `G` is affine. -/
  isAffineZ : IsAffine Z.left
  /-- The smooth model is affine. -/
  isAffineY : IsAffine Y.left
  /-- The map into the source scheme is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion i.left
  /-- The map into the source scheme is of finite presentation. -/
  finitePresentation : Scheme.Hom.FinitePresentation i.left
  /-- The auxiliary module is quasicoherent. -/
  quasicoherent : G.IsQuasicoherent
  /-- The auxiliary module is of finite type. -/
  finiteType : G.IsFiniteType
  /-- Pushing the auxiliary module forward along `i` recovers the source module. -/
  moduleIso : Nonempty (F ≅ (Scheme.Modules.pushforward i.left).obj G)
  /-- The morphism from the auxiliary scheme to the smooth model is finite. -/
  finite : IsFinite π.left
  /-- The structure morphism of the model is smooth. -/
  smooth : Smooth Y.hom
  /-- The fibres of the model over the base are geometrically irreducible. -/
  geometricallyIrreducible : GeometricallyIrreducible Y.hom
  /-- Every model fibre has dimension equal to the support dimension of `F` over `s`. -/
  fiberDimension :
    Y.hom.fiberDimension = fun _ ↦ fiberSupportDimension X.hom F s

namespace IsOneStepDevissageOver

/-- Regard explicit one-step data satisfying `IsOneStepDevissageOver` as the canonical bundled
`OneStepDevissage`. -/
def toOneStepDevissage {S : Scheme.{u}} {X : Over S} {F : X.left.Modules} {s : S}
    {Z Y : Over S} {i : Z ⟶ X} {π : Z ⟶ Y} {G : Z.left.Modules}
    (D : IsOneStepDevissageOver X F s Z Y i π G) :
    @OneStepDevissage S X F D.locallyOfFiniteType D.sourceQuasicoherent D.sourceFiniteType s :=
  @OneStepDevissage.mk S X F D.locallyOfFiniteType D.sourceQuasicoherent D.sourceFiniteType s
    Z Y i π G D.isAffineS D.isAffineX D.isAffineZ D.isAffineY D.isClosedImmersion
    D.finitePresentation D.quasicoherent D.finiteType D.moduleIso D.finite D.smooth
    D.geometricallyIrreducible D.fiberDimension

/-- The canonical one-step dévissage recovered from explicit data has the supplied auxiliary
scheme. -/
theorem toOneStepDevissage_Z {S : Scheme.{u}} {X : Over S} {F : X.left.Modules} {s : S}
    {Z Y : Over S} {i : Z ⟶ X} {π : Z ⟶ Y} {G : Z.left.Modules}
    (D : IsOneStepDevissageOver X F s Z Y i π G) :
    @OneStepDevissage.Z S X F D.locallyOfFiniteType D.sourceQuasicoherent
      D.sourceFiniteType s D.toOneStepDevissage = Z := sorry

/-- The chosen data of a canonical `OneStepDevissage` satisfy the corresponding explicit
one-step predicate. -/
theorem ofOneStepDevissage {S : Scheme.{u}} {X : Over S} {F : X.left.Modules}
    [LocallyOfFiniteType X.hom] [F.IsQuasicoherent] [F.IsFiniteType] {s : S}
    (D : OneStepDevissage X F s) :
    IsOneStepDevissageOver X F s D.Z D.Y D.i D.π D.G := sorry

end IsOneStepDevissageOver

namespace OneStepDevissageAt

variable {S : Scheme.{u}} {X : Over S} {F : X.left.Modules}
  [LocallyOfFiniteType X.hom] [F.IsQuasicoherent] [F.IsFiniteType] {x : X.left}

/-- Forgetting the distinguished-point conditions of a one-step dévissage at `x` gives a
one-step dévissage over `X.hom x`. -/
theorem isOneStepDevissageOver (D : OneStepDevissageAt X F x) :
    IsOneStepDevissageOver X F (X.hom x) D.toOneStepDevissage.Z
      D.toOneStepDevissage.Y D.toOneStepDevissage.i D.toOneStepDevissage.π
      D.toOneStepDevissage.G := sorry

end OneStepDevissageAt

namespace CompleteDevissageOver

/-- One chosen stage in a complete dévissage over `s`. -/
structure Stage (S : Scheme.{u}) (s : S) where
  /-- The scheme carrying the auxiliary module. -/
  Z : Over S
  /-- The smooth model over the base. -/
  Y : Over S
  /-- The finite morphism from the auxiliary scheme to the model. -/
  π : Z ⟶ Y
  /-- The finite-type quasicoherent module on `Z`. -/
  G : Z.left.Modules
  /-- The rank of the finite free source of the comparison map. -/
  rank : ℕ
  /-- The comparison from a finite free module to the pushforward of `G`. -/
  α : (SheafOfModules.freeFin rank : Y.left.Modules) ⟶
    (Scheme.Modules.pushforward π.left).obj G
  /-- The chosen generic point of the fibre of `Y` over `s`. -/
  ξ : Y.hom.fiber s
  /-- The chosen point is generic in the fibre. -/
  isGeneric : IsGenericPoint ξ (Set.univ : Set (Y.hom.fiber s))
  /-- Every generic point of the fibre is the chosen point. -/
  uniqueGeneric :
    ∀ η : Y.hom.fiber s, IsGenericPoint η (Set.univ : Set (Y.hom.fiber s)) → η = ξ
  /-- The comparison map is an isomorphism after passing to the chosen generic-point fibre. -/
  fiberBijective :
    Function.Bijective (Scheme.Modules.fiberMap α (Y.hom.fiberι s ξ))

namespace Stage

/-- Build a complete-dévisage stage from its schemes, module, comparison map, and generic-point
data. -/
def ofComponents {S : Scheme.{u}} {s : S}
    (Z Y : Over S) (π : Z ⟶ Y) (G : Z.left.Modules) (rank : ℕ)
    (α : (SheafOfModules.freeFin rank : Y.left.Modules) ⟶
      (Scheme.Modules.pushforward π.left).obj G)
    (ξ : Y.hom.fiber s)
    (isGeneric : IsGenericPoint ξ (Set.univ : Set (Y.hom.fiber s)))
    (uniqueGeneric :
      ∀ η : Y.hom.fiber s, IsGenericPoint η (Set.univ : Set (Y.hom.fiber s)) → η = ξ)
    (fiberBijective :
      Function.Bijective (Scheme.Modules.fiberMap α (Y.hom.fiberι s ξ))) :
    Stage S s where
  Z := Z
  Y := Y
  π := π
  G := G
  rank := rank
  α := α
  ξ := ξ
  isGeneric := isGeneric
  uniqueGeneric := uniqueGeneric
  fiberBijective := fiberBijective

/-- Rebuilding a stage from all of its components returns the original chosen stage. -/
theorem ofComponents_self {S : Scheme.{u}} {s : S} (D : Stage S s) :
    ofComponents D.Z D.Y D.π D.G D.rank D.α D.ξ D.isGeneric D.uniqueGeneric
      D.fiberBijective = D := sorry

/-- The canonical residue-field fibre map induced by the comparison map of a stage. -/
def genericFiberMap {S : Scheme.{u}} {s : S} (D : Stage S s) :=
  Scheme.Modules.fiberMap D.α (D.Y.hom.fiberι s D.ξ)

/-- `genericFiberMap` is the fibre map induced by the stage comparison `α`. -/
theorem genericFiberMap_def {S : Scheme.{u}} {s : S} (D : Stage S s) :
    D.genericFiberMap = Scheme.Modules.fiberMap D.α (D.Y.hom.fiberι s D.ξ) := sorry

/-- The selected point of a stage is the unique generic point of its fibre over `s`. -/
theorem genericPoint_spec {S : Scheme.{u}} {s : S} (D : Stage S s) :
    IsGenericPoint D.ξ (Set.univ : Set (D.Y.hom.fiber s)) ∧
      ∀ η : D.Y.hom.fiber s,
        IsGenericPoint η (Set.univ : Set (D.Y.hom.fiber s)) → η = D.ξ := sorry

/-- The comparison map of a stage is bijective on the selected generic-point fibre. -/
theorem fiberMap_bijective {S : Scheme.{u}} {s : S} (D : Stage S s) :
    Function.Bijective D.genericFiberMap := sorry

end Stage

end CompleteDevissageOver

/-- A finite nonempty complete dévissage of `F / X / S` over `s`. -/
structure CompleteDevissageOver {S X : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] (s : S) where
  /-- The final zero-based index of the nonempty chain. -/
  last : ℕ
  /-- The chosen stages of the dévissage. -/
  stage : Fin (last + 1) → CompleteDevissageOver.Stage S s
  /-- The initial closed immersion into `X`. -/
  initial : (stage 0).Z ⟶ Over.mk f
  /-- The first stage is a one-step dévissage of `F / X / S` over `s`. -/
  initialStep : IsOneStepDevissageOver (Over.mk f) F s
    (stage 0).Z (stage 0).Y initial (stage 0).π (stage 0).G
  /-- The immersion from the next auxiliary scheme into the preceding smooth model. -/
  transition (i : Fin last) : (stage i.succ).Z ⟶ (stage i.castSucc).Y
  /-- Every later stage is a one-step dévissage of the preceding comparison cokernel. -/
  transitionStep (i : Fin last) :
    IsOneStepDevissageOver (stage i.castSucc).Y (cokernel (stage i.castSucc).α) s
      (stage i.succ).Z (stage i.succ).Y (transition i)
      (stage i.succ).π (stage i.succ).G
  /-- The cokernel of the comparison map at the final stage is zero. -/
  terminal : IsZero (cokernel (stage (Fin.last last)).α)

namespace CompleteDevissageOver

/-- Assemble a complete dévissage from its explicit finite family of stages, immersions, and
one-step and terminal conditions. -/
def ofStages {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] {s : S}
    (last : ℕ) (stage : Fin (last + 1) → Stage S s)
    (initial : (stage 0).Z ⟶ Over.mk f)
    (initialStep : IsOneStepDevissageOver (Over.mk f) F s
      (stage 0).Z (stage 0).Y initial (stage 0).π (stage 0).G)
    (transition : (i : Fin last) → (stage i.succ).Z ⟶ (stage i.castSucc).Y)
    (transitionStep : ∀ i : Fin last,
      IsOneStepDevissageOver (stage i.castSucc).Y (cokernel (stage i.castSucc).α) s
        (stage i.succ).Z (stage i.succ).Y (transition i)
        (stage i.succ).π (stage i.succ).G)
    (terminal : IsZero (cokernel (stage (Fin.last last)).α)) :
    CompleteDevissageOver f F s where
  last := last
  stage := stage
  initial := initial
  initialStep := initialStep
  transition := transition
  transitionStep := transitionStep
  terminal := terminal

/-- Rebuilding a complete dévissage from all of its stages and conditions returns the original
chosen dévissage. -/
theorem ofStages_self {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] {s : S}
    (D : CompleteDevissageOver f F s) :
    ofStages D.last D.stage D.initial D.initialStep D.transition D.transitionStep D.terminal = D := sorry

/-- The initial stage is a one-step dévissage of the original module. -/
theorem initialStep_spec {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] {s : S}
    (D : CompleteDevissageOver f F s) :
    IsOneStepDevissageOver (Over.mk f) F s (D.stage 0).Z (D.stage 0).Y D.initial
      (D.stage 0).π (D.stage 0).G := sorry

/-- Every stage after the first is a one-step dévissage of the preceding comparison cokernel. -/
theorem transitionStep_spec {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] {s : S}
    (D : CompleteDevissageOver f F s) (i : Fin D.last) :
    IsOneStepDevissageOver (D.stage i.castSucc).Y (cokernel (D.stage i.castSucc).α) s
      (D.stage i.succ).Z (D.stage i.succ).Y (D.transition i)
      (D.stage i.succ).π (D.stage i.succ).G := sorry

/-- At every stage, the chosen point is the unique generic point of the fibre over `s`. -/
theorem genericPoint_spec {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] {s : S}
    (D : CompleteDevissageOver f F s) (i : Fin (D.last + 1)) :
    IsGenericPoint (D.stage i).ξ (Set.univ : Set ((D.stage i).Y.hom.fiber s)) ∧
      ∀ η : (D.stage i).Y.hom.fiber s,
        IsGenericPoint η (Set.univ : Set ((D.stage i).Y.hom.fiber s)) →
          η = (D.stage i).ξ := sorry

/-- At every stage, the comparison map is bijective on the unique generic-point fibre. -/
theorem fiberMap_bijective {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] {s : S}
    (D : CompleteDevissageOver f F s) (i : Fin (D.last + 1)) :
    Function.Bijective (D.stage i).genericFiberMap := sorry

/-- The cokernel of the final comparison map in a complete dévissage is zero. -/
theorem terminalCokernel_isZero {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] {s : S}
    (D : CompleteDevissageOver f F s) :
    IsZero (cokernel (D.stage (Fin.last D.last)).α) := sorry

end CompleteDevissageOver

end AlgebraicGeometry.Scheme.Modules
