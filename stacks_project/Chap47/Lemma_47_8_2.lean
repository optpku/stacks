module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.DerivedTorsionColimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 47.8.2 (1): if `I` is finitely generated, then the underlying derived `A`-module
of `RΓ_I(K)` is a homotopy colimit of the canonical system
`RHom_A(A / I ^ (n + 1), K)`. -/
@[stacks 0954] #check
  (CategoryTheory.ModuleCat.IdealPowerTorsion.derivedTorsionIsHomotopyColimit :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
      (K : DerivedCategory (ModuleCat.{u} A)),
      CategoryTheory.HomotopyColimit.IsOf
        ((CategoryTheory.DerivedCategory.IdealPower.system I).rightOp ⋙
          CategoryTheory.DerivedCategory.InternalHom.RHom.sourceFunctor K)
        ((CategoryTheory.ModuleCat.IdealPowerTorsion.derivedInclusion I).obj
          ((CategoryTheory.ModuleCat.IdealPowerTorsion.derivedTorsion I).obj K)))

/- Lemma 47.8.2 (2): for every `q : ℤ`, the `q`th cohomology module of `RΓ_I(K)` is
isomorphic to the colimit of the modules
`Ext_A^q(A / I ^ (n + 1), K) = H^q(RHom_A(A / I ^ (n + 1), K))`. -/
@[stacks 0954] #check
  (CategoryTheory.ModuleCat.IdealPowerTorsion.derivedTorsionHomologyIsColimit :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
      (K : DerivedCategory (ModuleCat.{u} A)) (q : ℤ),
      CategoryTheory.IsIsomorphic
        ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
          ((CategoryTheory.ModuleCat.IdealPowerTorsion.derivedInclusion I).obj
            ((CategoryTheory.ModuleCat.IdealPowerTorsion.derivedTorsion I).obj K)))
        (CategoryTheory.Limits.colimit
          (((CategoryTheory.DerivedCategory.IdealPower.system I).rightOp ⋙
              CategoryTheory.DerivedCategory.InternalHom.RHom.sourceFunctor K) ⋙
            _root_.DerivedCategory.homologyFunctor (ModuleCat.{u} A) q)))
