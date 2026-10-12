/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap108.Lemma_108_4_9_InjectiveResolution
public import stacks_project.Chap108.Lemma_108_4_9_LocalHomCarrier
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent

/-! Injective replacement of the structure-sheaf unit in the original module universe. -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.StructureSheaf

variable {S : Scheme.{u}}

/-- Genuine replacement of the source's structure-sheaf unit, in X.Modules itself. -/
noncomputable def unitReplacement (X : AlgebraicSpace S) : CochainComplex X.Modules ℤ :=
  AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site.spaceResolutionComplex X (structureSheaf X) (𝟙_ X.Modules)

/-- The original source's precise O_X[0] maps to that replacement without a new hypothesis. -/
noncomputable def unitReplacementMap (X : AlgebraicSpace S) :
    (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj (𝟙_ X.Modules) ⟶
      unitReplacement X :=
  AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site.spaceResolutionMap X (structureSheaf X) (𝟙_ X.Modules)

/-- K-injectivity of the actual source-typed replacement. -/
theorem unitReplacementKInjective (X : AlgebraicSpace S) :
    (unitReplacement X).IsKInjective :=
  AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site.spaceResolutionKInjective X (structureSheaf X) (𝟙_ X.Modules)

/-- The source-typed comparison is a genuine quasi-isomorphism. -/
theorem unitReplacementQuasiIso (X : AlgebraicSpace S) : QuasiIso (unitReplacementMap X) :=
  AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site.spaceResolutionQuasiIso X (structureSheaf X) (𝟙_ X.Modules)

/-- The size certificate specializes to original X.Modules local morphisms. -/
theorem localHomSmall (X : AlgebraicSpace S) (M N : X.Modules) (U : smallEtaleSite X) :
    Small.{u} (M.over U ⟶ N.over U) := AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site.spaceLocalHomSmall X (structureSheaf X) M N U

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.StructureSheaf
