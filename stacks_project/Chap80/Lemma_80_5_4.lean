module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.LocallyQuasiFinite
import StacksCheckRecall

/-!
# Locally quasi-finite morphisms representable by algebraic spaces

A morphism from a scheme over `S` to a functor on `(Over S)ᵒᵖ` that is
representable by algebraic spaces and locally quasi-finite is representable
by schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 80.5.4: a locally quasi-finite morphism from a scheme to a presheaf,
representable by algebraic spaces, is representable by schemes. -/
@[stacks 0AHV] #check
  (AlgebraicGeometry.AlgebraicSpace.relativelyRepresentable_of_locallyQuasiFinite :
    ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {X : Over S}
      (a : yoneda.obj X ⟶ F) (ha : representableByAlgebraicSpaces a)
      (h_locallyOfFiniteType :
        ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ F), LocallyOfFiniteType (ha.pullbackHom ξ))
      (h_locallyQuasiFinite :
        ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ F), LocallyQuasiFinite (ha.pullbackHom ξ)),
      yoneda.relativelyRepresentable a)
