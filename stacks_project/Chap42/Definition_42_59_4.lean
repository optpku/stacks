module

public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin
public import stacks_project.Chap42.Situation_42_7_1
public import stacks_project.Chap42.Remark_42_35_5_Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/- Definition 42.59.4: a morphism has a Gysin map exactly when it factors as an
immersion followed by a smooth morphism. -/
@[stacks 0FF3] #check
  (AlgebraicGeometry.BivariantClass.HasGysinMap.iff_exists :
    ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y),
      AlgebraicGeometry.BivariantClass.HasGysinMap f ↔
        ∃ (middle : Over S) (i : X ⟶ middle) (g : middle ⟶ Y),
          IsImmersion i.left ∧ Smooth g.left ∧ i ≫ g = f)

/-- The Gysin class attached to explicit immersion and smooth classes is their homogeneous
bivariant composition, transported along the chosen factorization equality. -/
noncomputable def bivariantGysinClassOfFactorization
    {S : Scheme.{u}} [_root_.AlgebraicGeometry.UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    (middle : Over S) [LocallyOfFiniteType middle.hom]
    (i : X ⟶ middle) (g : middle ⟶ Y)
    (isImmersion : IsImmersion i.left) (isSmooth : Smooth g.left)
    (hfac : i ≫ g = f) {p q : ℤ}
    (immersionGysin : BivariantClass δ i p)
    (smoothPullback : BivariantClass δ g q) :
    BivariantClass δ f (p + q) :=
  hfac ▸ BivariantClass.comp δ i g immersionGysin smoothPullback

end AlgebraicGeometry.BivariantClass
