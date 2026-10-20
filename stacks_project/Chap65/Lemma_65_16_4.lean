module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase.RestrictionProduct
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite

universe u

/- Lemma 65.16.4
Restriction of an fppf sheaf along a morphism of base schemes is algebraic if and only if
its product with the representable presheaf of that morphism is algebraic.
-/
@[stacks 04SH] #check (AlgebraicGeometry.AlgebraicSpace.isAlgebraicSpace_restriction_iff_prod :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') {F' : (Over S')ᵒᵖ ⥤ Type u},
    Presheaf.IsSheaf (Scheme.fppfTopology.over S') F' →
      (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace
          (AlgebraicGeometry.AlgebraicSpace.baseChangePresheaf g F') ↔
        AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace (yoneda.obj (Over.mk g) ⨯ F')))
