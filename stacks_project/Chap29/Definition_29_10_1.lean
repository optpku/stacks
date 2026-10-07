module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Radicial
import StacksCheckRecall

@[expose] public section

open CategoryTheory.MorphismProperty

universe u

/- Definition 29.10.1: A scheme morphism is universally injective when every
base change is injective on underlying topological spaces. It is radicial when
it is injective on points and every induced residue-field map is purely
inseparable. -/
@[stacks 01S3] #check (AlgebraicGeometry.radicial_iff :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
    AlgebraicGeometry.Radicial f ↔ Function.Injective f ∧
      ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable)

#check (AlgebraicGeometry.universallyInjective_iff :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
    AlgebraicGeometry.UniversallyInjective f ↔
      universally (AlgebraicGeometry.topologically (Function.Injective ·)) f)

#check (AlgebraicGeometry.radicial_iff_universallyInjective :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
    AlgebraicGeometry.Radicial f ↔ AlgebraicGeometry.UniversallyInjective f)
