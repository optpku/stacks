module

public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Factorization
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
open AlgebraicGeometry.BivariantClass.Gysin

universe u

/- Lemma 42.59.3: the Gysin class of a local complete intersection morphism is independent
of its immersion–smooth factorization, including varying normal ranks and smooth dimensions. -/
@[stacks 0FF2] #check (AlgebraicGeometry.BivariantClass.gysin_eq_of_factorization :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    {P : Over S} [LocallyOfFiniteType P.hom]
    (i : X ⟶ P) (g : P ⟶ Y) [IsRegularImmersion i.left] [Smooth g.left]
    (hfac : i ≫ g = f)
    (e : Scheme.Modules.dual (normalSheaf i.left) ≅ conormalSheaf i.left)
    (D : ClosedDeformation X.hom (i.left.coborderRange.ι ≫ P.hom)
      i.left.liftCoborder
      (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
      (normalBundle i.left e).toCoborder)
    {P' : Over S} [LocallyOfFiniteType P'.hom]
    (i' : X ⟶ P') (g' : P' ⟶ Y) [IsRegularImmersion i'.left] [Smooth g'.left]
    (hfac' : i' ≫ g' = f)
    (e' : Scheme.Modules.dual (normalSheaf i'.left) ≅ conormalSheaf i'.left)
    (D' : ClosedDeformation X.hom (i'.left.coborderRange.ι ≫ P'.hom)
      i'.left.liftCoborder
      (by rw [← Category.assoc, i'.left.liftCoborder_ι]; exact Over.w i')
      (normalBundle i'.left e').toCoborder),
    (fun p : ℤ ↦ factorizationClassDegree δ f i g hfac e D p) =
      (fun p : ℤ ↦ factorizationClassDegree δ f i' g' hfac' e' D' p))
