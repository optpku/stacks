module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.MorphismFunctor
public import stacks_project.Chap99.«99_7_1_1_Functor»

/-!
# Relative morphisms on schemes over `B`

The functor `Mor_B(Z, X)` on `(Sch/B)^op`, sending a scheme `T` over `B` to
the type of morphisms `Z_T ⟶ X_T` over `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.Quot (SchemesOver)

noncomputable section

universe u

/- Lemma 99.12.1: the relative-morphism functor on schemes over the base. -/
#check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.mor :
  ∀ {S : Scheme.{u}} {Z B X : AlgebraicSpace S} (z : Z ⟶ B) (x : X ⟶ B),
    (SchemesOver B)ᵒᵖ ⥤ Type (u + 1))
