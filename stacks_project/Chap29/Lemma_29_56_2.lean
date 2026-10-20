module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Locus
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.56.2: the finite-type quasi-finite locus of an arbitrary scheme morphism is open. -/
@[stacks 01TI] #check (AlgebraicGeometry.Scheme.Hom.FiniteType.isOpen_quasiFiniteAt :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      IsOpen {x : X | AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt f x})

/- The morphism induced on this locus is locally of finite type and locally quasi-finite. -/
#check (AlgebraicGeometry.Scheme.Hom.FiniteType.locallyQuasiFinite_quasiFiniteLocus :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.LocallyOfFiniteType
          ((AlgebraicGeometry.Scheme.Hom.FiniteType.quasiFiniteLocus f).ι ≫ f) ∧
        AlgebraicGeometry.LocallyQuasiFinite
          ((AlgebraicGeometry.Scheme.Hom.FiniteType.quasiFiniteLocus f).ι ≫ f))
