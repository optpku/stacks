module

public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Factorization
public import ReasLib.AlgebraicGeometry.BivariantClass.Commutation

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom.VirtualNormalBundle Gysin

/-- An immersion–smooth factorization of a local complete intersection morphism admits
a regular immersion and a normal-sheaf deformation realization such that every restricted
integer-degree Gysin coefficient commutes with every bivariant class over the new base. -/
theorem gysin_restrict_commute
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
    (h : Y'' ⟶ Y') [LocallyOfFiniteType h.left] :
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
            inferInstance inferInstance inferInstance f ι σ hreg hσ hfac e D p)) :=
  sorry

end AlgebraicGeometry.BivariantClass
