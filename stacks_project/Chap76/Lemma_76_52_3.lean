module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative.Etale
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived

universe u

/- Lemma 76.52.3. For a flat, locally finitely presented morphism of algebraic spaces,
a quasi-coherent derived complex is relatively perfect if and only if it passes every
étale-square test, one surjective étale-square test, or every affine derived-sections test. -/
@[stacks 0DKQ] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo.tfae :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Flat f] [LocallyOfFinitePresentation f] {E : ModuleDerived X},
      derivedQuasiCoherentModuleProperty X E →
        List.TFAE [IsPerfectRelativeTo f E, IsPerfectRelativeTo.everyEtaleSquare f E,
          IsPerfectRelativeTo.existsSurjectiveEtaleSquare f E,
          IsPerfectRelativeTo.everyAffineSections f E])
