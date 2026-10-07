module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseSystem
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Pullback
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! Compatible systems of complexes of abelian étale sheaves. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {I : Type u} [Preorder I]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ i : I, HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ {S T : Scheme.{u}} (f : T ⟶ S) (G : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (smallEtalePullback f).op.HasLeftKanExtension G]
variable [hAdj : ∀ {S T : Scheme.{u}} (f : T ⟶ S),
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]

/-- Transition inverse image preserves finite limits. -/
instance transitionPullback_preservesFiniteLimits {i j : I} (hij : i ≤ j) :
    PreservesFiniteLimits (transitionPullback D hij) :=
  by infer_instance

/-- Transition inverse image preserves zero morphisms. -/
instance transitionPullback_preservesZeroMorphisms {i j : I} (hij : i ≤ j) :
    (transitionPullback D hij).PreservesZeroMorphisms := by
  infer_instance

/-- Transition inverse image lifted to cochain complexes. -/
abbrev transitionPullbackComplex {i j : I} (hij : i ≤ j) :
    CochainComplex (Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}) ℤ ⥤
      CochainComplex (Sheaf (D.obj (OrderDual.toDual j)).smallEtaleTopology AddCommGrpCat.{u}) ℤ :=
  (transitionPullback D hij).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Successive complex inverse images are canonically identified with composite inverse image. -/
def transitionPullbackComplexCompIso {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    transitionPullbackComplex D hij ⋙ transitionPullbackComplex D hjk ≅
      transitionPullbackComplex D (le_trans hij hjk) :=
  NatIso.mapHomologicalComplex (transitionPullbackCompIso D hij hjk) (ComplexShape.up ℤ)

/-- A compatible system of cochain complexes of abelian étale sheaves. -/
structure AbelianSheafComplexSystem where
  /-- The cochain complex at stage `i`. -/
  obj (i : I) :
    CochainComplex (Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}) ℤ
  /-- The transition map from stage `i` to stage `j`. -/
  transition {i j : I} (hij : i ≤ j) :
    (transitionPullbackComplex D hij).obj (obj i) ⟶ obj j
  /-- Compatibility of transitions with three composable indices. -/
  transition_comp {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    (transitionPullbackComplexCompIso D hij hjk).hom.app (obj i) ≫
        transition (le_trans hij hjk) =
      (transitionPullbackComplex D hjk).map (transition hij) ≫ transition hjk

namespace AbelianSheafComplexSystem

variable {D : OrderDual I ⥤ Scheme.{u}}

/-- Construct a compatible complex system from its stages and transitions. -/
def of
    (obj : (i : I) →
      CochainComplex (Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}) ℤ)
    (transition : ∀ {i j : I} (hij : i ≤ j),
      (transitionPullbackComplex D hij).obj (obj i) ⟶ obj j)
    (transition_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
      (transitionPullbackComplexCompIso D hij hjk).hom.app (obj i) ≫
          transition (le_trans hij hjk) =
        (transitionPullbackComplex D hjk).map (transition hij) ≫ transition hjk) :
    AbelianSheafComplexSystem D where
  obj := obj
  transition := transition
  transition_comp := transition_comp

/-- The constructor has the supplied stage object. -/
theorem of_obj
    (obj : (i : I) →
      CochainComplex (Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}) ℤ)
    (transition : ∀ {i j : I} (hij : i ≤ j),
      (transitionPullbackComplex D hij).obj (obj i) ⟶ obj j)
    (transition_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
      (transitionPullbackComplexCompIso D hij hjk).hom.app (obj i) ≫
          transition (le_trans hij hjk) =
        (transitionPullbackComplex D hjk).map (transition hij) ≫ transition hjk)
    (i : I) : (of obj transition transition_comp).obj i = obj i := sorry

/-- The constructor has the supplied transition map. -/
theorem of_transition
    (obj : (i : I) →
      CochainComplex (Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}) ℤ)
    (transition : ∀ {i j : I} (hij : i ≤ j),
      (transitionPullbackComplex D hij).obj (obj i) ⟶ obj j)
    (transition_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
      (transitionPullbackComplexCompIso D hij hjk).hom.app (obj i) ≫
          transition (le_trans hij hjk) =
        (transitionPullbackComplex D hjk).map (transition hij) ≫ transition hjk)
    {i j : I} (hij : i ≤ j) :
    (of obj transition transition_comp).transition hij = transition hij := sorry

/-- The constructor recovers both the supplied stage objects and transition maps. -/
theorem of_spec
    (obj : (i : I) →
      CochainComplex (Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}) ℤ)
    (transition : ∀ {i j : I} (hij : i ≤ j),
      (transitionPullbackComplex D hij).obj (obj i) ⟶ obj j)
    (transition_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
      (transitionPullbackComplexCompIso D hij hjk).hom.app (obj i) ≫
          transition (le_trans hij hjk) =
        (transitionPullbackComplex D hjk).map (transition hij) ≫ transition hjk) :
    (∀ i, (of obj transition transition_comp).obj i = obj i) ∧
      (∀ {i j : I} (hij : i ≤ j),
        (of obj transition transition_comp).transition hij = transition hij) := sorry

/-- Degreewise evaluation produces a compatible abelian sheaf system. -/
def degreewiseSheafSystem (F : AbelianSheafComplexSystem D) (n : ℤ) :
    AbelianSheafSystem D where
  obj i := (F.obj i).X n
  transition hij := by simpa [transitionPullbackComplex] using (F.transition hij).f n
  transition_comp hij hjk := sorry

/-- The degreewise system has the expected stage object. -/
theorem degreewiseSheafSystem_obj (F : AbelianSheafComplexSystem D) (n : ℤ) (i : I) :
    (degreewiseSheafSystem F n).obj i = (F.obj i).X n := sorry

variable (c : Cone D)
variable [HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable (F : AbelianSheafComplexSystem D)

/-- Cone inverse image preserves finite limits. -/
instance conePullback_preservesFiniteLimits (i : I)
    [HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}] :
    PreservesFiniteLimits (conePullback D c i) :=
  let hSource : HasSheafify
      (((Functor.const (OrderDual I)).obj c.pt).obj (OrderDual.toDual i)).smallEtaleTopology
        AddCommGrpCat.{u} := by
    change HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}
    infer_instance
  @AlgebraicGeometry.Scheme.Etale.smallEtalePullbackAbelian_preservesFiniteLimits
    _ _ _ (c.π.app (OrderDual.toDual i)) inferInstance hSource

/-- Cone inverse image preserves zero morphisms. -/
instance conePullback_preservesZeroMorphisms (i : I)
    [HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}] :
    (conePullback D c i).PreservesZeroMorphisms := by
  exact Functor.preservesZeroMorphisms_of_preserves_terminal_object

/-- Complex inverse images along a cone projection. -/
abbrev conePullbackComplex (i : I)
    [HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}] :
    CochainComplex (Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}) ℤ ⥤
      CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u}) ℤ :=
  (conePullback D c i).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The inverse-image complex diagram retains original transitions and adjoins identities. -/
def inverseImageComplexDiagram (F : AbelianSheafComplexSystem D)
    [∀ i : I, HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}] :
    PreorderWithAdjoinedIdentities I ⥤
      CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u}) ℤ :=
  PreorderWithAdjoinedIdentities.lift
    (fun i => (conePullbackComplex (D := D) c i).obj (F.obj i))
    (fun {i j} hij =>
      (NatIso.mapHomologicalComplex (conePullbackCompIso D c hij) (ComplexShape.up ℤ)).inv.app
          (F.obj i) ≫ (conePullbackComplex (D := D) c j).map (F.transition hij)) sorry

/-- The colimit of the inverse-image complex diagram. -/
def colimitInverseImageComplex (F : AbelianSheafComplexSystem D)
    [∀ i : I, HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasColimit (inverseImageComplexDiagram c F)] :
    CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u}) ℤ :=
  colimit (inverseImageComplexDiagram c F)

/-- The canonical inclusion of a stage complex into the colimit. -/
def colimitInverseImageComplex_ι (i : I)
    [∀ i : I, HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasColimit (inverseImageComplexDiagram (D := D) c F)] :
    (inverseImageComplexDiagram (D := D) c F).obj i ⟶ colimitInverseImageComplex c F :=
  colimit.ι (inverseImageComplexDiagram (D := D) c F) i

/-- The stage inclusion is the corresponding colimit leg. -/
theorem colimitInverseImageComplex_ι_eq (i : I)
    [∀ i : I, HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasColimit (inverseImageComplexDiagram (D := D) c F)] :
    colimitInverseImageComplex_ι c F i = colimit.ι (inverseImageComplexDiagram (D := D) c F) i := sorry

end AbelianSheafComplexSystem

end AlgebraicGeometry.Scheme.Etale

end
