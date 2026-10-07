module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Normal
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

/- Definition 37.20.1 (1): a scheme morphism with locally Noetherian fibres is normal
at `x` exactly when it is flat at `x` and its residue-field fibre is geometrically
normal at the distinguished point `f.asFiber x`. -/
@[stacks 0390] #check (AlgebraicGeometry.Scheme.Hom.NormalAt :
  {X Y : Scheme.{u}} → (X ⟶ Y) → X → Prop)

#check (AlgebraicGeometry.Scheme.Hom.normalAt_iff :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X),
    f.NormalAt x ↔
      f.flatAt x ∧
        SchemeOverField.geometricallyNormalAt
          (Over.mk (f.fiberToSpecResidueField (f x))) (f.asFiber x))

/- Definition 37.20.1 (2): a scheme morphism with locally Noetherian fibres is normal
exactly when it is normal at every point of its source. -/
@[stacks 0390] #check (AlgebraicGeometry.Normal :
  {X Y : Scheme.{u}} → (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.normal_iff_forall_normalAt :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    AlgebraicGeometry.Normal f ↔ ∀ x : X, f.NormalAt x)
