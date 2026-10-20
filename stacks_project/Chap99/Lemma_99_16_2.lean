module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.SelfHomFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative.BaseChange

/-!
# Lemma 99.16.2: relative base convention

Local erratum: in the source's assumptions (1) and (2), `S` and `s ∈ S`
must be `Y` and a point of `Y`. The arbitrary base change is `V ⟶ Y`,
so relative perfectness and fibre vanishing are then relative to `V`.
This is the specialization `K = E` of Lemma 99.16.1 with vanishing locus
all of `Y`. The original uploaded source is preserved unchanged.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open scoped DerivedExt

noncomputable section

universe u

section

variable {S : Scheme.{u}} {X Y V : AlgebraicSpace S} (f : X ⟶ Y)
variable [Proper f] [Flat f] [FinitePresentation f]
variable (E : ModuleDerived X) (g : V ⟶ Y)

/- Lemma 99.16.2 (1): A `Y`-perfect complex remains `V`-perfect after arbitrary
base change `V ⟶ Y`, using the approved relative-base correction. -/
@[stacks 0DLD] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo.baseChange f g E :
    IsPerfectRelativeTo f E →
      IsPerfectRelativeTo (Limits.pullback.snd f g) (baseChangePullback f g E))

end

/- Lemma 99.16.2 (2): Negative self-Ext vanishing on every field-valued fibre over
`Y` persists on fibres over the new base `V`. -/
@[stacks 0DLD] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.fiberNegativeSelfExtVanish_baseChange :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] (E : ModuleDerived X),
    IsPerfectRelativeTo f E →
    (∀ y : FieldValuedPoint Y, fiberNegativeExtVanish f E E y) →
    ∀ {V : AlgebraicSpace S} (g : V ⟶ Y) (v : FieldValuedPoint V),
    fiberNegativeExtVanish (Limits.pullback.snd f g)
      (baseChangePullback f g E) (baseChangePullback f g E) v)

/- Lemma 99.16.2 (3): All negative self-Ext groups vanish after arbitrary base
change for a `Y`-perfect complex with fibrewise vanishing. -/
@[stacks 0DLD] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.negativeSelfExt_eq_zero :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] (E : ModuleDerived X),
    IsPerfectRelativeTo f E →
    (∀ y : FieldValuedPoint Y, fiberNegativeExtVanish f E E y) →
    ∀ {V : AlgebraicSpace S} (g : V ⟶ Y) (i : ℤ), i < 0 →
    Subsingleton (Ext⁽i⁾(baseChangePullback f g E, baseChangePullback f g E)))

/- Lemma 99.16.2 (4): The full derived self-Hom presheaf on algebraic spaces over
`Y` is represented by an affine, finitely presented algebraic space over `Y`.
Relative perfectness and fibrewise vanishing use the approved `Y`-relative correction. -/
@[stacks 0DLD] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.selfHomFunctorOver_isAffineFinitePresentation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] (E : ModuleDerived X),
    IsPerfectRelativeTo f E →
    (∀ y : FieldValuedPoint Y, fiberNegativeExtVanish f E E y) →
    ∃ (F : AlgebraicSpace S) (π : F ⟶ Y),
      Affine π ∧ FinitePresentation π ∧
        Nonempty (selfHomFunctorOver f E ≅ yoneda.obj (Over.mk π)))

/- The same representability assertion restricted to schemes over `Y`. -/
#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.selfHomFunctor_isAffineFinitePresentation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] (E : ModuleDerived X),
    IsPerfectRelativeTo f E →
    (∀ y : FieldValuedPoint Y, fiberNegativeExtVanish f E E y) →
    IsAffineFinitePresentationOver (selfHomFunctor f E))
