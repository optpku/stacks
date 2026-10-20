module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Kunneth
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf
open CategoryTheory.DerivedCategory
open Opposite
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {k : Type u} [Field k] [IsSepClosed k]
variable (X Y : SchemeOverField k)
variable [IsProper X.hom]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
variable [HasPullback X.hom Y.hom]

section

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [((pullback X.hom Y.hom).smallEtaleTopology.W
    (A := AddCommGrpCat.{u})).IsMonoidal]
variable [MonoidalPreadditive AddCommGrpCat.{u}]
variable [∀ (K L : CochainComplex AddCommGrpCat.{u} ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor AddCommGrpCat.{u}) (ComplexShape.up ℤ)]
variable [hAbTensor : DerivedTensor.Right.Has (C := AddCommGrpCat.{u})]
variable [MonoidalPreadditive
    (Sheaf (pullback X.hom Y.hom).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ (K L : CochainComplex
      (Sheaf (pullback X.hom Y.hom).smallEtaleTopology AddCommGrpCat.{u}) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor
        (Sheaf (pullback X.hom Y.hom).smallEtaleTopology AddCommGrpCat.{u}))
      (ComplexShape.up ℤ)]
variable [hXYTensor :
    DerivedTensor.Right.Has
      (C := Sheaf (pullback X.hom Y.hom).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ Z : Scheme.{u},
    ((sheafSections Z.smallEtaleTopology AddCommGrpCat.{u}).obj
      (op (globalEtale Z))).Additive]
variable [∀ Z : Scheme.{u},
    Functor.HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((sheafSections Z.smallEtaleTopology AddCommGrpCat.{u}).obj
          (op (globalEtale Z))))
      (HomologicalComplex.quasiIso
        (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]

/- Lemma 59.97.2 (1): the proper-factor étale Künneth formula. -/
@[stacks 0F14] #check (AlgebraicGeometry.Scheme.Etale.rGamma_kunneth X Y :
  ∀
    (E : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})) E)
    (K : DerivedCategory.Plus (Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u})),
    Nonempty
      ((RightDerived.Cochain.functor
            ((sheafSections (pullback X.hom Y.hom).smallEtaleTopology
                AddCommGrpCat.{u}).obj
              (op (globalEtale (pullback X.hom Y.hom))))).obj
          (DerivedCategory.Plus.ι.obj
              ((etaleDerivedInverseImage (pullback.fst X.hom Y.hom)).obj E) ⊗ᴸ
            DerivedCategory.Plus.ι.obj
              ((etaleDerivedInverseImage (pullback.snd X.hom Y.hom)).obj K)) ≅
        ((RightDerived.Cochain.functor
              ((sheafSections X.left.smallEtaleTopology AddCommGrpCat.{u}).obj
                (op (globalEtale X.left)))).obj
            (DerivedCategory.Plus.ι.obj E) ⊗ᴸ
          (RightDerived.Cochain.functor
              ((sheafSections Y.left.smallEtaleTopology AddCommGrpCat.{u}).obj
                (op (globalEtale Y.left)))).obj
            (DerivedCategory.Plus.ι.obj K))))

end

section

variable (n : ℕ) [NeZero n]
variable [Algebraic Y]
variable [∀ Z : Scheme.{u},
    HasSheafify Z.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [HasDerivedCategory (ModuleCat.{u} (ZMod n))]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    PreservesFiniteLimits (zmodSheafPullback h n)]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B), (zmodSheafPullback h n).Additive]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B), (zmodSheafPushforward h n).Additive]
variable [((pullback X.hom Y.hom).smallEtaleTopology.W
    (A := ModuleCat.{u} (ZMod n))).IsMonoidal]
variable [MonoidalPreadditive (ModuleCat.{u} (ZMod n))]
variable [∀ (K L : CochainComplex (ModuleCat.{u} (ZMod n)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (ModuleCat.{u} (ZMod n))) (ComplexShape.up ℤ)]
variable [hModTensor :
    DerivedTensor.Right.Has (C := ModuleCat.{u} (ZMod n))]
variable [MonoidalPreadditive
    (Sheaf (pullback X.hom Y.hom).smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [∀ (K L : CochainComplex
      (Sheaf (pullback X.hom Y.hom).smallEtaleTopology (ModuleCat.{u} (ZMod n))) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor
        (Sheaf (pullback X.hom Y.hom).smallEtaleTopology (ModuleCat.{u} (ZMod n))))
      (ComplexShape.up ℤ)]
variable [hXYModTensor :
    DerivedTensor.Right.Has
      (C := Sheaf (pullback X.hom Y.hom).smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [∀ Z : Scheme.{u},
    ((sheafSections Z.smallEtaleTopology (ModuleCat.{u} (ZMod n))).obj
      (op (globalEtale Z))).Additive]
variable [∀ Z : Scheme.{u},
    Functor.HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((sheafSections Z.smallEtaleTopology (ModuleCat.{u} (ZMod n))).obj
          (op (globalEtale Z))))
      (HomologicalComplex.quasiIso
        (Sheaf Z.smallEtaleTopology (ModuleCat.{u} (ZMod n))) (ComplexShape.up ℤ))]

/- Lemma 59.97.2 (2): the proper-factor étale Künneth formula. -/
@[stacks 0F14] #check (AlgebraicGeometry.Scheme.Etale.rGamma_kunneth_zmod X Y n :
  ∀
    (E : DerivedCategory
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (K : DerivedCategory
      (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} (ZMod n)))),
    Nonempty
      ((RightDerived.Cochain.functor
            ((sheafSections (pullback X.hom Y.hom).smallEtaleTopology
                (ModuleCat.{u} (ZMod n))).obj
              (op (globalEtale (pullback X.hom Y.hom))))).obj
          ((zmodDerivedInverseImage (pullback.fst X.hom Y.hom) n).obj E ⊗ᴸ
            (zmodDerivedInverseImage (pullback.snd X.hom Y.hom) n).obj K) ≅
        ((RightDerived.Cochain.functor
              ((sheafSections X.left.smallEtaleTopology
                  (ModuleCat.{u} (ZMod n))).obj
                (op (globalEtale X.left)))).obj E ⊗ᴸ
          (RightDerived.Cochain.functor
              ((sheafSections Y.left.smallEtaleTopology
                  (ModuleCat.{u} (ZMod n))).obj
                (op (globalEtale Y.left)))).obj K)))

end

end AlgebraicGeometry.Scheme.Etale

end
