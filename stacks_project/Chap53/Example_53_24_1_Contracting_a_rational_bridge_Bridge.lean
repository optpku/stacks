/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.SeparableDegree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Intersection
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Union
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Complement
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Immersion
public import stacks_project.Chap53.Definition_53_19_1_Nodal
public import stacks_project.Chap53.Definition_53_8_1_Genus

public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalBridge.Contraction

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

#check (AlgebraicGeometry.RationalBridge.componentScheme :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k),
    irreducibleComponents X.left → SchemeOverField k)

#check (AlgebraicGeometry.RationalBridge.SectionDegreeTwo :
  ∀ {k : Type u} [Field k] (C D : SchemeOverField k), (D.left ⟶ C.left) → Prop)

#check (AlgebraicGeometry.RationalBridge.sectionDegree_spec :
  ∀ {k : Type u} [Field k] {X : SchemeOverField k} (B : RationalBridge X),
    RationalBridge.sectionRank (RationalBridge.componentScheme X B.component)
      (RationalBridge.intersectionScheme X B.component)
      (RationalBridge.intersectionToComponent X B.component) = 2)
