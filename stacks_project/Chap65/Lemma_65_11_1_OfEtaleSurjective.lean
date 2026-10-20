module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSurjective

/-!
# Algebraic spaces from representable étale-surjective atlases

An fppf sheaf on `Sch/S` equipped with a representable, surjective, and étale map from a
scheme over `S` is an algebraic space: the representable-diagonal axiom is automatic.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ofEtaleSurjective :
  ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u},
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) F →
    ∀ {U : Over S} (p : yoneda.obj U ⟶ F),
      (over (@Etale ⊓ @Surjective)).presheaf p → AlgebraicSpace S)
