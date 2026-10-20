module

import StacksCheckRecall

public import stacks_project.Chap42.Lemma_42_59_5
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Commutation

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom.VirtualNormalBundle Gysin

/- Lemma 42.59.7: every bivariant class commutes with the restricted Gysin class of a
local complete intersection morphism admitting an immersion–smooth factorization.
This is expressed coefficientwise in every integer degree, allowing varying normal ranks
and smooth relative dimensions. Regularity, the normal-sheaf bidual identification and a
deformation realization are asserted to exist; the assembled factorization coefficients
represent the Gysin class independently of that realization. The canonical common pullback
in `Commute` accounts for the left cartesian square. -/
@[stacks 0FF6] #check (AlgebraicGeometry.BivariantClass.gysin_restrict_commute :
  ∀
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' Y'' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    [LocallyOfFiniteType Y''.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    {P : Over S} [LocallyOfFiniteType P.hom]
    (ι : X ⟶ P) (σ : P ⟶ Y) (hι : IsImmersion ι.left)
    [hσ : Smooth σ.left] (hfac : ι ≫ σ = f)
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType f'.left]
    (square : IsPullback i.left f'.left f.left g.left)
    (h : Y'' ⟶ Y') [LocallyOfFiniteType h.left],
    ∃ hreg : IsRegularImmersion ι.left,
    ∃ e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
      Scheme.Hom.conormalSheaf ι.left,
    ∃ D : ClosedDeformation X.hom (ι.left.coborderRange.ι ≫ P.hom)
      ι.left.liftCoborder
      (by rw [← Category.assoc, ι.left.liftCoborder_ι]; exact Over.w ι)
      (@normalBundle X.left P.left ι.left hreg e).toCoborder,
    ∀ (p q : ℤ) (c : BivariantClass δ h q),
      Commute δ h f' c
        (restrict δ i f' g square p
          (@factorizationClassDegree S inferInstance δ inferInstance X Y P
            inferInstance inferInstance inferInstance f ι σ hreg hσ hfac e D p)))

end AlgebraicGeometry.BivariantClass
