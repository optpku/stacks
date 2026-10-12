/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import stacks_project.Chap74.Definition_74_20_1_SmoothLocal
public import stacks_project.Chap74.Definition_74_21_1_EtaleSmoothLocal

/-!
# Étale-smooth locality on source-and-target for standard morphism properties

Étale, Stacks locally quasi-finite, and unramified morphisms of algebraic
spaces are étale-smooth local on the source-and-target. Any property that is
smooth local on the source-and-target is a fortiori étale-smooth local.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Etale

/-- Étaleness of morphisms of algebraic spaces is étale-smooth local on the
source-and-target. -/
instance isEtaleSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsEtaleSmoothLocalAtSourceAndTarget (@Etale S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Etale

namespace AlgebraicGeometry.AlgebraicSpace.FiniteType

/-- Locally quasi-finite morphisms of algebraic spaces, in the Stacks sense of
locally of finite type and locally quasi-finite, are étale-smooth local on the
source-and-target. -/
instance locallyQuasiFiniteIsEtaleSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsEtaleSmoothLocalAtSourceAndTarget
      (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FiniteType

namespace AlgebraicGeometry.AlgebraicSpace.Unramified

/-- Unramifiedness of morphisms of algebraic spaces is étale-smooth local on the
source-and-target. -/
instance isEtaleSmoothLocalAtSourceAndTarget {S : Scheme.{u}} :
    IsEtaleSmoothLocalAtSourceAndTarget
      (@Unramified S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Unramified

namespace AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget

/-- A morphism property of algebraic spaces that is smooth local on the
source-and-target is a fortiori étale-smooth local on the source-and-target. -/
instance (priority := 50) of_isSmoothLocalAtSourceAndTarget {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} [IsSmoothLocalAtSourceAndTarget P] :
    IsEtaleSmoothLocalAtSourceAndTarget P :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget
