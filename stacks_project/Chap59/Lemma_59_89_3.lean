module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.DerivedSmooth
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

/- Lemma 59.89.3: Derived étale base change along a directed inverse limit of
smooth schemes with affine transition morphisms holds for quasi-compact,
quasi-separated morphisms and bounded-below coefficients whose cohomology
stalks are torsion of orders invertible on the base. -/
@[stacks 0F09] #check
  (AlgebraicGeometry.Scheme.Hom.derivedBaseChange_isIso_of_smoothInverseLimit :
    ∀
    {I : Type u} [Preorder I] [h_nonempty : Nonempty I]
    [h_directed : IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (DS : OrderDual I ⥤ Scheme.{u})
    [h_affine : ∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap DS hij)]
    (gi : ∀ i : I, DS.obj (OrderDual.toDual i) ⟶ S)
    [h_smooth : ∀ i : I, Smooth (gi i)]
    (hgi : ∀ {i j : I} (hij : i ≤ j),
      OrderDualInverseSystem.transitionMap DS hij ≫ gi i = gi j)
    (cS : Cone DS) (hcS : IsLimit cS) (g : cS.pt ⟶ S)
    (hg : ∀ i : I, cS.π.app (OrderDual.toDual i) ≫ gi i = g)
    {X : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {X' : Scheme.{u}} (f' : X' ⟶ cS.pt) (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsTorsionWithOrdersInvertibleOn.{u, u + 1} S :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) E),
    IsIso (BaseChange.derivedMapOfCommSq f g f' g' h_cart.toCommSq
      (DerivedCategory.Plus.ι.obj E)))

#check
  (AlgebraicGeometry.Scheme.Hom.derivedBaseChange_isIso_of_smoothInverseLimit_pullback :
    ∀
    {I : Type u} [Preorder I] [h_nonempty : Nonempty I]
    [h_directed : IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (DS : OrderDual I ⥤ Scheme.{u})
    [h_affine : ∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap DS hij)]
    (gi : ∀ i : I, DS.obj (OrderDual.toDual i) ⟶ S)
    [h_smooth : ∀ i : I, Smooth (gi i)]
    (hgi : ∀ {i j : I} (hij : i ≤ j),
      OrderDualInverseSystem.transitionMap DS hij ≫ gi i = gi j)
    (cS : Cone DS) (hcS : IsLimit cS) (g : cS.pt ⟶ S)
    (hg : ∀ i : I, cS.π.app (OrderDual.toDual i) ≫ gi i = g)
    {X : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [HasPullback g f]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsTorsionWithOrdersInvertibleOn.{u, u + 1} S :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) E),
    IsIso (BaseChange.derivedMapOfCommSq f g (pullback.fst g f) (pullback.snd g f)
      (IsPullback.of_hasPullback g f).flip.toCommSq (DerivedCategory.Plus.ι.obj E)))

end
