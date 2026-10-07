module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.EmbeddedPoints

@[expose] public section

universe u v w

/- Definition 31.4.1: canonical embedded-associated, embedded-point, and embedded-component owners. -/
@[stacks 05AK] #check (@AlgebraicGeometry.Scheme.Modules.embeddedAssociatedAt :
  {X : AlgebraicGeometry.Scheme.{u}} → X.Modules → X → Prop)

#check (@Ideal.torsionOf_map_eq_of_injective :
  {R : Type u} → [CommRing R] →
    {M : Type v} → [AddCommGroup M] → [Module R M] →
      {N : Type w} → [AddCommGroup N] → [Module R N] →
        {f : M →ₗ[R] N} → Function.Injective f → (m : M) →
          Ideal.torsionOf R N (f m) = Ideal.torsionOf R M m)
#check (@Ideal.IsAssociatedToModule :
  (R : Type u) → (M : Type v) → [CommRing R] → [AddCommGroup M] →
    [Module R M] → Ideal R → Prop)
#check (@associatedPrimesOfModule :
  (R : Type u) → (M : Type v) → [CommRing R] → [AddCommGroup M] →
    [Module R M] → Set (Ideal R))
#check (@AlgebraicGeometry.RingedSpace.stalkModuleCat :
  {X : AlgebraicGeometry.RingedSpace.{u}} → X.Modules → (x : X) →
    ModuleCat (X.presheaf.stalk x))
#check (@AlgebraicGeometry.Scheme.Modules.associatedPoints :
  {X : AlgebraicGeometry.Scheme.{u}} → X.Modules → Set X)
#check (@AlgebraicGeometry.Scheme.Modules.mem_associatedPoints_iff :
  {X : AlgebraicGeometry.Scheme.{u}} → (F : X.Modules) → (x : X) →
    (x ∈ AlgebraicGeometry.Scheme.Modules.associatedPoints F ↔
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
        associatedPrimesOfModule (X.presheaf.stalk x)
          (AlgebraicGeometry.RingedSpace.stalkModuleCat F (x : X.toRingedSpace))))
#check (@AlgebraicGeometry.Scheme.associatedPoints :
  (X : AlgebraicGeometry.Scheme.{u}) → Set X)
#check (@AlgebraicGeometry.Scheme.mem_associatedPoints_iff :
  (X : AlgebraicGeometry.Scheme.{u}) → (x : X) →
    (x ∈ X.associatedPoints ↔
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
        associatedPrimesOfModule (X.presheaf.stalk x)
          (AlgebraicGeometry.RingedSpace.stalkModuleCat
            (SheafOfModules.unit X.ringCatSheaf :
              AlgebraicGeometry.RingedSpace.Modules X.toRingedSpace)
            (x : X.toRingedSpace))))
#check (@AlgebraicGeometry.Scheme.Modules.embeddedAssociatedAt.mem_associatedPoints :
  {X : AlgebraicGeometry.Scheme.{u}} → (F : X.Modules) → {x : X} →
    F.embeddedAssociatedAt x → x ∈ F.associatedPoints)
#check (@AlgebraicGeometry.Scheme.Modules.embeddedAssociatedAt.exists_specializing_associated :
  {X : AlgebraicGeometry.Scheme.{u}} → (F : X.Modules) → {x : X} →
    F.embeddedAssociatedAt x →
      ∃ y : X, y ∈ F.associatedPoints ∧ y ≠ x ∧ y ⤳ x)
#check (@AlgebraicGeometry.Scheme.Modules.embeddedAssociatedAt_iff :
  {X : AlgebraicGeometry.Scheme.{u}} → (F : X.Modules) → (x : X) →
    (F.embeddedAssociatedAt x ↔
      x ∈ F.associatedPoints ∧
        ∃ y : X, y ∈ F.associatedPoints ∧ y ≠ x ∧ y ⤳ x))
#check (@AlgebraicGeometry.Scheme.Modules.embeddedAssociatedPoints :
  {X : AlgebraicGeometry.Scheme.{u}} → X.Modules → Set X)
#check (@AlgebraicGeometry.Scheme.Modules.mem_embeddedAssociatedPoints_iff :
  {X : AlgebraicGeometry.Scheme.{u}} → (F : X.Modules) → (x : X) →
    (x ∈ F.embeddedAssociatedPoints ↔ F.embeddedAssociatedAt x))
#check (@AlgebraicGeometry.Scheme.Modules.embeddedAssociatedPoints_eq_empty_iff :
  {X : AlgebraicGeometry.Scheme.{u}} → (F : X.Modules) →
    (F.embeddedAssociatedPoints = (∅ : Set X) ↔
      ∀ x : X, ¬ F.embeddedAssociatedAt x))
#check (@AlgebraicGeometry.Scheme.embeddedPoint :
  (X : AlgebraicGeometry.Scheme.{u}) → X → Prop)
#check (@AlgebraicGeometry.Scheme.embeddedPoint_iff :
  (X : AlgebraicGeometry.Scheme.{u}) → (x : X) →
    (X.embeddedPoint x ↔
      x ∈ X.associatedPoints ∧
        ∃ y : X, y ∈ X.associatedPoints ∧ y ≠ x ∧ y ⤳ x))
#check (@AlgebraicGeometry.Scheme.embeddedPoint.mem_associatedPoints :
  (X : AlgebraicGeometry.Scheme.{u}) → {x : X} →
    X.embeddedPoint x → x ∈ X.associatedPoints)
#check (@AlgebraicGeometry.Scheme.embeddedPoint.exists_specializing_associated :
  (X : AlgebraicGeometry.Scheme.{u}) → {x : X} →
    X.embeddedPoint x →
      ∃ y : X, y ∈ X.associatedPoints ∧ y ≠ x ∧ y ⤳ x)
#check (@AlgebraicGeometry.Scheme.embeddedPoints :
  (X : AlgebraicGeometry.Scheme.{u}) → Set X)
#check (@AlgebraicGeometry.Scheme.mem_embeddedPoints_iff :
  (X : AlgebraicGeometry.Scheme.{u}) → (x : X) →
    (x ∈ X.embeddedPoints ↔ X.embeddedPoint x))
#check (@AlgebraicGeometry.Scheme.embeddedPoints_eq_empty_iff :
  (X : AlgebraicGeometry.Scheme.{u}) →
    (X.embeddedPoints = (∅ : Set X) ↔ ∀ x : X, ¬ X.embeddedPoint x))
#check (@AlgebraicGeometry.Scheme.isEmbeddedComponent :
  (X : AlgebraicGeometry.Scheme.{u}) →
    TopologicalSpace.IrreducibleCloseds X → Prop)
#check (@AlgebraicGeometry.Scheme.isEmbeddedComponent_iff :
  (X : AlgebraicGeometry.Scheme.{u}) →
    (Z : TopologicalSpace.IrreducibleCloseds X) →
      (X.isEmbeddedComponent Z ↔
        ∃ x : X, X.embeddedPoint x ∧
          (Z : Set X) = closure ({x} : Set X)))
#check (@AlgebraicGeometry.Scheme.isEmbeddedComponent.exists_embeddedPoint :
  (X : AlgebraicGeometry.Scheme.{u}) →
    {Z : TopologicalSpace.IrreducibleCloseds X} → X.isEmbeddedComponent Z →
      ∃ x : X, X.embeddedPoint x ∧
        (Z : Set X) = closure ({x} : Set X))
