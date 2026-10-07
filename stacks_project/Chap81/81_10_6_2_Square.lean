module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap67.Definition_67_13_2_InverseImage
public import stacks_project.Chap67.Lemma_67_13_5_Complement
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage

/-!
# Open complement square for formal glueing of modules

In the formal-glueing situation, `U = X \ Z` is the open complement of a closed
immersion `i : Z ⟶ X`, and `V` is the open inverse image of `U` along `f : Y ⟶ X`,
i.e. the working pullback model of `Y \ f⁻¹(Z)`. The resulting square is cartesian.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing

/-- The open complement `U = X \ Z` of a closed immersion `i : Z ⟶ X`. -/
abbrev U {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    AlgebraicSpace S :=
  closedImmersionComplement i

/-- The open immersion `j : U ⟶ X` of the complement of `i`. -/
abbrev j {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    U i ⟶ X :=
  closedImmersionComplementι i

/-- The working pullback model of `Y \ f⁻¹(Z)`, as the open inverse image of `j`
along `f`. -/
abbrev V {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] : AlgebraicSpace S :=
  openInverseImage f (j i)

/-- The open immersion `j' : V ⟶ Y`. -/
abbrev j' {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] : V f i ⟶ Y :=
  openInverseImageι f (j i)

/-- The restricted morphism `f|_V : V ⟶ U`. -/
abbrev restrictF {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] : V f i ⟶ U i :=
  openInverseImageTo f (j i)

/-- The open-complement square is commutative, as the pullback condition on the
functor-of-points fibre product (Hom of algebraic spaces is a natural
transformation). -/
theorem square_comm {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] :
    restrictF f i ≫ j i = j' f i ≫ f :=
  (pullback.condition :
      pullback.fst (toFunctorOfPoints f) (toFunctorOfPoints (j i)) ≫
        toFunctorOfPoints f =
      pullback.snd (toFunctorOfPoints f) (toFunctorOfPoints (j i)) ≫
        toFunctorOfPoints (j i)).symm

/-- The working pullback `V` is isomorphic to the closed-immersion complement
`Y \ f⁻¹(Z)`. -/
theorem V_isComplement {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] :
    IsIsomorphic (V f i) (closedImmersionComplement (inverseImageι f i)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing
