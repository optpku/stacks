module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_6_3_UniversallyOpen
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_36_4_Syntomic
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap74.Definition_74_20_1_SmoothLocal

/-!
# Smooth locality on source-and-target for standard morphism properties

Flat, locally of finite presentation, locally of finite type, universally open,
syntomic, and smooth morphisms of algebraic spaces are smooth local on the
source-and-target.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Flat

/-- Flatness of morphisms of algebraic spaces is smooth local on the
source-and-target. -/
instance isSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsSmoothLocalAtSourceAndTarget (@Flat S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Flat

namespace AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation

/-- Local finite presentation of morphisms of algebraic spaces is smooth local
on the source-and-target. -/
instance isSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsSmoothLocalAtSourceAndTarget
      (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation

namespace AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType

/-- Local finite type of morphisms of algebraic spaces is smooth local on the
source-and-target. -/
instance isSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsSmoothLocalAtSourceAndTarget
      (@LocallyOfFiniteType S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType

namespace AlgebraicGeometry.AlgebraicSpace.UniversallyOpen

/-- Universal openness of morphisms of algebraic spaces is smooth local on the
source-and-target. -/
instance isSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsSmoothLocalAtSourceAndTarget
      (@UniversallyOpen S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.UniversallyOpen

namespace AlgebraicGeometry.AlgebraicSpace.Syntomic

/-- Syntomicity of morphisms of algebraic spaces is smooth local on the
source-and-target. -/
instance isSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsSmoothLocalAtSourceAndTarget
      (@Syntomic S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Syntomic

namespace AlgebraicGeometry.AlgebraicSpace.Smooth

/-- Smoothness of morphisms of algebraic spaces is smooth local on the
source-and-target. -/
instance isSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsSmoothLocalAtSourceAndTarget
      (@Smooth S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Smooth
