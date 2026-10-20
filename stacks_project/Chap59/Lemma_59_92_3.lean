module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.ZMod
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u

/- Lemma 59.92.3: Proper base change for unbounded derived small-étale ZMod-module sheaves. -/
@[stacks 0F0C] #check (AlgebraicGeometry.Scheme.Etale.zmodDerivedBaseChangeHom_isIso_of_isProper :
  ∀ {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ) [NeZero n]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))),
    IsIso (zmodDerivedBaseChangeHom f g f' g' h_cart n E))

#check (AlgebraicGeometry.Scheme.Etale.zmodDerivedBaseChangeHom_isIso_of_isProper_pullback :
  ∀ {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y)
    [HasPullback g f] (n : ℕ) [NeZero n]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf (pullback g f).smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))),
    IsIso
      (zmodDerivedBaseChangeHom f g (pullback.fst g f) (pullback.snd g f)
        (IsPullback.of_hasPullback g f).flip n E))
