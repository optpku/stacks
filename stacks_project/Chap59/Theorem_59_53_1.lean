module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HigherDirectImageStalk
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (s : GeometricPoint S)
variable (Rsh : Type u) [CommRing Rsh]
variable [Algebra (S.presheaf.stalk s.image) Rsh]
variable [IsStrictHenselizationOf (S.presheaf.stalk s.image) Rsh]

#check (AlgebraicGeometry.Scheme.Etale.henselizedFiber f s Rsh : Scheme.{u})

#check (AlgebraicGeometry.Scheme.Etale.henselizedFiber_def f s Rsh :
  henselizedFiber f s Rsh = pullback f (strictHenselizationMap S s Rsh))

#check (AlgebraicGeometry.Scheme.Etale.henselizedFiberToX f s Rsh :
  henselizedFiber f s Rsh ⟶ X)

#check (AlgebraicGeometry.Scheme.Etale.henselizedFiberToX_def f s Rsh :
  henselizedFiberToX f s Rsh = pullback.fst f (strictHenselizationMap S s Rsh))

variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasExt (Sheaf (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [Abelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable [Abelian (Sheaf (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u})]
variable [EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf (henselizedFiber f s Rsh).smallEtaleTopology
    AddCommGrpCat.{u})]
variable [HasDerivedCategory AddCommGrpCat.{u}]
variable [(etaleAbelianPushforward f).Additive]
variable [((smallEtalePullback (henselizedFiberToX f s Rsh)).sheafPushforwardContinuous
    AddCommGrpCat.{u} X.smallEtaleTopology
    (henselizedFiber f s Rsh).smallEtaleTopology).IsRightAdjoint]
variable [((smallEtalePullback (henselizedFiberToX f s Rsh)).sheafPullback AddCommGrpCat.{u}
    X.smallEtaleTopology (henselizedFiber f s Rsh).smallEtaleTopology).Additive]
variable [PreservesFiniteLimits
    ((smallEtalePullback (henselizedFiberToX f s Rsh)).sheafPullback AddCommGrpCat.{u}
      X.smallEtaleTopology (henselizedFiber f s Rsh).smallEtaleTopology)]
variable [PreservesFiniteColimits
    ((smallEtalePullback (henselizedFiberToX f s Rsh)).sheafPullback AddCommGrpCat.{u}
      X.smallEtaleTopology (henselizedFiber f s Rsh).smallEtaleTopology)]
variable [(sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u} ⋙
    s.toSmallEtalePoint.presheafFiber).Additive]
variable [PreservesFiniteLimits
    (sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u} ⋙
      s.toSmallEtalePoint.presheafFiber)]
variable [PreservesFiniteColimits
    (sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u} ⋙
      s.toSmallEtalePoint.presheafFiber)]
variable [IsGrothendieckAbelian
    (Sheaf (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u})]
variable [(siteAbelianSectionsFunctor (henselizedFiber f s Rsh).smallEtaleTopology
    (globalEtale (henselizedFiber f s Rsh))).Additive]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (siteAbelianSectionsFunctor (henselizedFiber f s Rsh).smallEtaleTopology
        (globalEtale (henselizedFiber f s Rsh))))
    (HomologicalComplex.quasiIso
      (Sheaf (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u})
      (ComplexShape.up ℤ))]

#check (AlgebraicGeometry.Scheme.Etale.henselizedSheafPullback f s Rsh :
  Sheaf X.smallEtaleTopology AddCommGrpCat.{u} →
    Sheaf (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u})

#check (AlgebraicGeometry.Scheme.Etale.henselizedDerivedPullback f s Rsh :
  DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) →
    DerivedCategory (Sheaf (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u}))

#check (AlgebraicGeometry.Scheme.Etale.henselizedDerivedGlobalSections f s Rsh :
  DerivedCategory (Sheaf (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u}) ⥤
    DerivedCategory AddCommGrpCat.{u})

/- Theorem 59.53.1: for a quasi-compact quasi-separated morphism of schemes,
the geometric stalks of higher direct images are the étale cohomology groups
of the strict-henselized fibre with inverse-image coefficients. The bounded-below
derived variants identify all integer-degree cohomology groups and the derived
stalk with derived global sections on that fibre. -/
@[stacks 03Q9] #check
  (AlgebraicGeometry.Scheme.Etale.higherDirectImage_stalk_eq_etaleCohomology f s Rsh :
    ∀ [QuasiCompact f] [QuasiSeparated f]
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ),
    IsIsomorphic
      (s.toSmallEtalePoint.sheafFiber.obj
        (Sheaf.higherDirectImage (smallEtalePullback f) F n))
      ((henselizedSheafPullback f s Rsh F).H'
        n (globalEtale (henselizedFiber f s Rsh))))

#check
  (AlgebraicGeometry.Scheme.Etale.derivedHigherDirectImage_stalk_eq_etaleCohomology f s Rsh :
    ∀ [QuasiCompact f] [QuasiSeparated f]
      (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
      (n : ℤ),
    IsIsomorphic
      (s.toSmallEtalePoint.sheafFiber.obj
        ((DerivedCategory.homologyFunctor
            (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) n).obj
          (DerivedCategory.Plus.ι.obj
            ((etaleAbelianPushforward f).rightDerivedFunctorPlus.obj K))))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((henselizedDerivedGlobalSections f s Rsh).obj
          (henselizedDerivedPullback f s Rsh (DerivedCategory.Plus.ι.obj K)))))

#check
  (AlgebraicGeometry.Scheme.Etale.derivedPushforward_stalk_eq_derivedGlobalSections f s Rsh :
    ∀ [QuasiCompact f] [QuasiSeparated f]
      (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})),
    IsIsomorphic
      ((sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u} ⋙
          s.toSmallEtalePoint.presheafFiber).mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj
          ((etaleAbelianPushforward f).rightDerivedFunctorPlus.obj K)))
      ((henselizedDerivedGlobalSections f s Rsh).obj
        (henselizedDerivedPullback f s Rsh (DerivedCategory.Plus.ι.obj K))))

end AlgebraicGeometry.Scheme.Etale

end
