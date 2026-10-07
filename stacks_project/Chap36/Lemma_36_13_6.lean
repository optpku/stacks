module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Extension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpace.Hom.IsFlat

noncomputable section

universe u

/- Lemma 36.13.6: for a perfect derived module on a quasi-compact open subscheme of an
affine scheme, adjoining a shifted finite locally free module produces the restriction of a
perfect derived module on the ambient scheme. -/
@[stacks 08EG] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.exists_finiteLocallyFree_biprod_extension :
    ∀ {X U : Scheme.{u}} [IsAffine X]
      (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (E : RingedSpace.ModuleDerived U.toRingedSpace)
      (hE : RingedSpace.ModuleDerived.IsPerfect E),
      ∃ (r : ℤ) (F : U.Modules) (hF : F.IsFiniteLocallyFree)
        (P : RingedSpace.ModuleDerived X.toRingedSpace)
        (e : (exactPullback j.toShHom).mapDerivedCategory.obj P ≅
          ((DerivedCategory.singleFunctor U.toRingedSpace.Modules 0).obj F)⟦-r⟧ ⊞ E),
        RingedSpace.ModuleDerived.IsPerfect P)
