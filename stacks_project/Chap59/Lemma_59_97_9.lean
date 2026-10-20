module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Kunneth
import StacksCheckRecall

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf CategoryTheory.DerivedCategory Opposite

universe u

/- Lemma 59.97.9: over a separably closed field, the étale Künneth formula holds for
arbitrary unbounded `ZMod n` complexes on finite-type schemes when `n` is positive and invertible. -/
@[stacks 0F1P] #check
  (AlgebraicGeometry.Scheme.Etale.rGamma_kunneth_zmod_of_finiteType :
    ∀ {k : Type u} [Field k] [IsSepClosed k],
    ∀ (X Y : SchemeOverField k),
    ∀ [Algebraic X] [Algebraic Y],
    ∀ [HasPullback X.hom Y.hom],
    ∀ (n : ℕ) [NeZero n],
    ∀ [∀ Z : Scheme.{u},
    HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} (ZMod n)))],
    ∀ [HasDerivedCategory (ModuleCat.{u} (ZMod n))],
    ∀ [∀ (K L : CochainComplex (ModuleCat.{u} (ZMod n)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (ModuleCat.TensorProduct.functor (ZMod n)) (ComplexShape.up ℤ)],
    ∀ [∀ E : DerivedCategory (ModuleCat.{u} (ZMod n)),
    Functor.HasLeftDerivedFunctor
      (Bifunctor.Right.sourceFunctor (ModuleCat.TensorProduct.functor (ZMod n)) E)
      (HomotopyCategory.quasiIso (ModuleCat.{u} (ZMod n)) (ComplexShape.up ℤ))],
    ∀ [∀ (K L : CochainComplex
      (Sheaf (pullback X.hom Y.hom).smallEtaleTopology (ModuleCat.{u} (ZMod n))) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (ModuleCat.TensorProduct.Sheaf.functor
        (pullback X.hom Y.hom).smallEtaleTopology (ZMod n)) (ComplexShape.up ℤ)],
    ∀ [∀ E : DerivedCategory
      (Sheaf (pullback X.hom Y.hom).smallEtaleTopology (ModuleCat.{u} (ZMod n))),
    Functor.HasLeftDerivedFunctor
      (Bifunctor.Right.sourceFunctor
        (ModuleCat.TensorProduct.Sheaf.functor
          (pullback X.hom Y.hom).smallEtaleTopology (ZMod n)) E)
      (HomotopyCategory.quasiIso
        (Sheaf (pullback X.hom Y.hom).smallEtaleTopology (ModuleCat.{u} (ZMod n)))
        (ComplexShape.up ℤ))],
    ∀ [∀ Z : Scheme.{u},
    ((sheafSections Z.smallEtaleTopology (ModuleCat.{u} (ZMod n))).obj
      (op (globalEtale Z))).Additive],
    ∀ [∀ Z : Scheme.{u},
    Functor.HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((sheafSections Z.smallEtaleTopology (ModuleCat.{u} (ZMod n))).obj
          (op (globalEtale Z))))
      (HomologicalComplex.quasiIso
        (Sheaf Z.smallEtaleTopology (ModuleCat.{u} (ZMod n))) (ComplexShape.up ℤ))],
    ∀(h_n : IsUnit (n : k))
    (E : DerivedCategory
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (K : DerivedCategory
      (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} (ZMod n)))),
    Nonempty
      ((RightDerived.Cochain.functor
            ((sheafSections (pullback X.hom Y.hom).smallEtaleTopology
                (ModuleCat.{u} (ZMod n))).obj
              (op (globalEtale (pullback X.hom Y.hom))))).obj
          (Bifunctor.Right.obj
            (ModuleCat.TensorProduct.Sheaf.functor
              (pullback X.hom Y.hom).smallEtaleTopology (ZMod n))
            ((zmodDerivedInverseImage (pullback.fst X.hom Y.hom) n).obj E)
            ((zmodDerivedInverseImage (pullback.snd X.hom Y.hom) n).obj K)) ≅
        Bifunctor.Right.obj (ModuleCat.TensorProduct.functor (ZMod n))
          ((RightDerived.Cochain.functor
              ((sheafSections X.left.smallEtaleTopology
                  (ModuleCat.{u} (ZMod n))).obj
                (op (globalEtale X.left)))).obj E)
          ((RightDerived.Cochain.functor
              ((sheafSections Y.left.smallEtaleTopology
                  (ModuleCat.{u} (ZMod n))).obj
                (op (globalEtale Y.left)))).obj K)))
