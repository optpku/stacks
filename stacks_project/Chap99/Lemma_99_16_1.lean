module

public import stacks_project.Chap99.Lemma_99_16_1_Hom
public import stacks_project.Chap99.Lemma_99_16_1_Open
public import stacks_project.Chap99.Lemma_99_16_1_Pullback

/-!
# Lemma 99.16.1

For a proper, flat, finitely presented morphism of algebraic spaces, the
locus in `|Y|` where negative fibre Ext-groups of a pseudo-coherent complex
and a `Y`-perfect complex vanish is an open subspace `W ⊂ Y`. Negative Ext
groups remain zero after any base change factoring through `W`, and the Hom
functor on `Spaces/W` is represented by an algebraic space affine of finite
presentation over `W`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable [Proper f] [Flat f] [FinitePresentation f]
variable (K E : ModuleDerived X) (hK : IsPseudoCoherent X K)
variable (hE : IsPerfectRelativeTo f E)

/-- Lemma 99.16.1 (1): a field-valued point of `Y` lies in `|W|` if and only if
the fibre Ext-groups `Ext⁽i⁾(K_y, E_y)` vanish for all `i < 0`. -/
@[stacks 0DLC]
theorem mem_negativeExtVanishingOpen_iff (p : FieldValuedPoint Y) :
    Points.mk p ∈ negativeExtVanishingOpen f K E hK hE ↔
      fiberNegativeExtVanish f K E p :=
  sorry

/-- Lemma 99.16.1 (2): if `V ⟶ Y` factors through `W`, then the Ext-groups
`Ext⁽i⁾(K_V, E_V)` vanish for all `i < 0`. -/
@[stacks 0DLC]
theorem negativeExt_eq_zero_of_factors {V : AlgebraicSpace S} (g : V ⟶ Y)
    (h : V ⟶ (negativeExtVanishing f K E hK hE).X)
    (hh : h ≫ (negativeExtVanishing f K E hK hE).ι = g) (i : ℤ) (hi : i < 0) :
    Subsingleton
      (Ext⁽i⁾(baseChangePullback f g K, baseChangePullback f g E)) :=
  sorry

/-- Lemma 99.16.1 (3): the functor `V ↦ Hom_{𝒪_{X_V}}(K_V, E_V)` on algebraic
spaces over `W` is represented by an algebraic space affine of finite
presentation over `W`. -/
@[stacks 0DLC]
theorem homFunctorOver_isAffineFinitePresentation :
    ∃ (F : AlgebraicSpace S) (π : F ⟶ (negativeExtVanishing f K E hK hE).X),
      Affine π ∧ FinitePresentation π ∧
        Nonempty (homFunctorOver f K E hK hE ≅ yoneda.obj (Over.mk π)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
