/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.GaloisRealization
public import ReasLib.AlgebraicGeometry.Scheme.Etale.OverField.Components

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.DiscreteContAction.OrbitDecomposition
open scoped FintypeCatDiscrete

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.Etale.GaloisRealization

variable (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
  [IsSepClosure K Ksep]
variable (Y : (Spec (.of K)).Etale)

/-- The original discrete Galois set of points of the given scheme. -/
abbrev sourceAction := (galoisFiber K Ksep).obj Y

/-- The native separably closed étale lifting construction gives a point over each
specified underlying scheme point. -/
def pointOver (y : Y.left) : Carrier (sourceAction K Ksep Y) := by
  letI : IsSepClosed Ksep := IsSepClosure.sep_closed K
  let f : Y.left ⟶ Spec (.of K) := Y.hom
  letI : Etale f := Y.prop
  let h := Scheme.exists_fac_of_etale_of_isSepClosed f
    (Spec.map (CommRingCat.ofHom (algebraMap K Ksep))) y (Subsingleton.elim _ _)
  exact Over.homMk (Classical.choose h) (Classical.choose_spec h).1

/-- The orbit attached to a point uses its actual native étale lift. -/
def pointIndex (y : Y.left) : OrbitIndex (sourceAction K Ksep Y) :=
  indexOf (sourceAction K Ksep Y) (pointOver K Ksep Y y)

/-- A geometric orbit remembers the underlying point of any of its representatives. -/
def orbitPoint (ω : OrbitIndex (sourceAction K Ksep Y)) : Y.left :=
  (Quotient.out ω).left (default : Spec (.of Ksep))

/-- Underlying scheme points index precisely the geometric Galois orbits. -/
def pointsOrbitEquiv : Y.left ≃ OrbitIndex (sourceAction K Ksep Y) where
  toFun := pointIndex K Ksep Y
  invFun := orbitPoint K Ksep Y
  left_inv := sorry
  right_inv := sorry

/-- Compose a point of the residue-field component with its actual inclusion. -/
def componentPoint (y : Y.left)
    (p : finiteEtaleSepFiber K Ksep (OverField.component Y y)) :
    Carrier (sourceAction K Ksep Y) :=
  Over.homMk (p.left ≫ Y.left.fromSpecResidueField y) (w := sorry)

/-- Points of one residue-field component have the same Galois orbit. -/
theorem componentPoint_mem (y : Y.left)
    (p : finiteEtaleSepFiber K Ksep (OverField.component Y y)) :
    componentPoint K Ksep Y y p ∈ (pointIndex K Ksep Y y).orbit := sorry

/-- The finite component-fibre map is the specified inclusion on its point carrier. -/
def componentOrbitForward (y : Y.left)
    (p : finiteEtaleSepFiber K Ksep (OverField.component Y y)) :
    (pointIndex K Ksep Y y).orbit :=
  ⟨componentPoint K Ksep Y y p, componentPoint_mem K Ksep Y y p⟩

/-- The underlying scheme point is constant on its Galois orbit. -/
theorem orbitPoint_eq (y : Y.left) (p : (pointIndex K Ksep Y y).orbit) :
    p.val.left (default : Spec (.of Ksep)) = y := sorry

/-- The prescribed orbit point lies in the residue-field open, with the actual
unique point of the residue spectrum as preimage. -/
theorem orbitPoint_range (y : Y.left) (p : (pointIndex K Ksep Y y).orbit) :
    Set.range p.val.left ⊆ Set.range (Y.left.fromSpecResidueField y) := by
  rintro _ ⟨z, rfl⟩
  refine ⟨default, ?_⟩
  rw [Y.left.fromSpecResidueField_apply]
  change Spec (.of Ksep) at z
  have hz : z = (default : Spec (.of Ksep)) := Subsingleton.elim _ _
  rw [hz, orbitPoint_eq K Ksep Y y p]

/-- Factor the specified point through the native open inverse of the component inclusion. -/
def componentOrbitInverse (y : Y.left) (p : (pointIndex K Ksep Y y).orbit) :
    finiteEtaleSepFiber K Ksep (OverField.component Y y) := by
  let lifted : Spec (.of Ksep) ⟶ Spec (Y.left.residueField y) :=
    @IsOpenImmersion.lift _ _ _ (Y.left.fromSpecResidueField y)
      (show Spec (.of Ksep) ⟶ Y.left from p.val.left)
      (OverField.component_isOpenImmersion Y y) (orbitPoint_range K Ksep Y y p)
  exact Over.homMk lifted (w := sorry)

/-- The finite Galois action on a component is its actual orbit action. -/
def componentOrbitIso (y : Y.left) :
    (finiteEtaleGaloisFiber K Ksep).obj (OverField.component Y y) ≅
      finiteOrbit (sourceAction K Ksep Y) (pointIndex K Ksep Y y) :=
  ObjectProperty.isoMk _ <| ObjectProperty.isoMk _ <|
    Action.mkIso
      (FintypeCat.equivEquivIso
        { toFun := componentOrbitForward K Ksep Y y
          invFun := componentOrbitInverse K Ksep Y y
          left_inv := sorry
          right_inv := sorry })
      (fun _ ↦ sorry)

/-- The finite classification unit and its inverse functor identify each actual
residue component with the scheme realizing its finite point orbit. -/
def componentRealizedIso (y : Y.left) :
    OverField.component Y y ≅
      orbitScheme K Ksep (sourceAction K Ksep Y) (pointIndex K Ksep Y y) :=
  (finiteEtaleGaloisEquivalence K Ksep).unitIso.app (OverField.component Y y) ≪≫
    (finiteEtaleGaloisEquivalence K Ksep).inverse.mapIso (componentOrbitIso K Ksep Y y)

/-- The same component comparison on its actual scheme carrier. -/
def componentRealizedSchemeIso (y : Y.left) :
    Spec (Y.left.residueField y) ≅
      (orbitScheme K Ksep (sourceAction K Ksep Y) (pointIndex K Ksep Y y)).left :=
  (MorphismProperty.Over.forget finiteEtaleMorphism ⊤ (Spec (.of K)) ⋙
    CategoryTheory.Over.forget (Spec (.of K))).mapIso (componentRealizedIso K Ksep Y y)

/-- Reindex the actual residue-field decomposition by geometric Galois orbits. -/
def unitSchemeIso : Y.left ≅ (object K Ksep (sourceAction K Ksep Y)).left :=
  (OverField.componentsIso Y).symm ≪≫
    Sigma.mapIso (componentRealizedSchemeIso K Ksep Y) ≪≫
    Sigma.reindex (pointsOrbitEquiv K Ksep Y)
      (fun ω ↦ (orbitScheme K Ksep (sourceAction K Ksep Y) ω).left)

/-- Both scheme maps preserve the specified structural morphism to the ground field. -/
def unitComponent : Y ≅ object K Ksep (sourceAction K Ksep Y) :=
  MorphismProperty.Over.isoMk (unitSchemeIso K Ksep Y) (by sorry)

/-- Actual realization unit, assembled from residue-field components and finite classification. -/
def unitIso : 𝟭 ((Spec (.of K)).Etale) ≅ galoisFiber K Ksep ⋙ functor K Ksep :=
  NatIso.ofComponents (unitComponent K Ksep) (fun _ ↦ sorry)

end AlgebraicGeometry.Scheme.Etale.GaloisRealization

end
