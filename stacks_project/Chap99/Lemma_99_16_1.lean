module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.NegativeExt
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.HomFunctor

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open scoped DerivedExt

noncomputable section

universe u

/- Lemma 99.16.1 (1): Field-valued point characterization of the negative Ext vanishing open. -/
@[stacks 0DLC] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.mem_negativeExtVanishingOpen_iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] (K E : ModuleDerived X)
    (hK : IsPseudoCoherent X K) (hE : IsPerfectRelativeTo f E),
    ∀ p : FieldValuedPoint Y,
      Points.mk p ∈ negativeExtVanishingOpen f K E hK hE ↔
        fiberNegativeExtVanish f K E p)

/- Lemma 99.16.1 (2): Negative Ext vanishes after every base change factoring through the open. -/
@[stacks 0DLC] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.negativeExt_eq_zero_of_factors :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] (K E : ModuleDerived X)
    (hK : IsPseudoCoherent X K) (hE : IsPerfectRelativeTo f E),
    ∀ {V : AlgebraicSpace S} (g : V ⟶ Y)
      (h : V ⟶ (negativeExtVanishing f K E hK hE).X)
      (hh : h ≫ (negativeExtVanishing f K E hK hE).ι = g) (i : ℤ) (hi : i < 0),
      Subsingleton (Ext⁽i⁾(baseChangePullback f g K, baseChangePullback f g E)))

/- Lemma 99.16.1 (3): The derived Hom presheaf on all algebraic spaces over the open is an fppf sheaf. -/
@[stacks 0DLC] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.homFunctorOver_isSheaf :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] (K E : ModuleDerived X)
    (hK : IsPseudoCoherent X K) (hE : IsPerfectRelativeTo f E),
    Presheaf.IsSheaf
      ((AlgebraicGeometry.AlgebraicSpace.fppfTopology S).over
        (negativeExtVanishing f K E hK hE).X)
      (homFunctorOver f K E hK hE))

/- Lemma 99.16.1 (4): The full derived Hom presheaf is represented by an affine, finitely presented algebraic space. -/
@[stacks 0DLC] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.homFunctorOver_isAffineFinitePresentation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] (K E : ModuleDerived X)
    (hK : IsPseudoCoherent X K) (hE : IsPerfectRelativeTo f E),
    ∃ (F : AlgebraicSpace S) (π : F ⟶ (negativeExtVanishing f K E hK hE).X),
      Affine π ∧ FinitePresentation π ∧
        Nonempty (homFunctorOver f K E hK hE ≅ yoneda.obj (Over.mk π)))
