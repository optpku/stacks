module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Coproduct
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/- Lemma 59.96.3 (1) - finite-cohomological-dimension derived direct image preserves coproducts. -/
@[stacks 0F11] #check
  (AlgebraicGeometry.Scheme.Etale.directImage_preservesCoproducts_of_finiteCohomologicalDimension :
    ∀ (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (n : ℕ) (hn : 0 < n)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (hcd : Hom.cohomologicalDimension f ≠ ⊤)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} (ZMod n)) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} (ZMod n)) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))) (ComplexShape.up ℤ))]
    (I : Type u)
    [HasColimitsOfShape (Discrete I)
      (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))]
    [HasColimitsOfShape (Discrete I)
      (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))))],
      PreservesColimitsOfShape (Discrete I)
        (RightDerived.Cochain.functor
          ((smallEtalePullback f).sheafPushforwardContinuous
            (ModuleCat.{u} (ZMod n)) Y.smallEtaleTopology X.smallEtaleTopology)))

/- Lemma 59.96.3 (2) - finite-cohomological-dimension derived global sections preserve coproducts. -/
@[stacks 0F11] #check
  (AlgebraicGeometry.Scheme.Etale.sections_preservesCoproducts_of_finiteCohomologicalDimension :
    ∀ [CompactSpace X] [QuasiSeparatedSpace X] (n : ℕ) (hn : 0 < n)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (hcd : cohomologicalDimension X ≠ ⊤)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (ModuleCat.{u} (ZMod n))]
    [((sheafSections X.smallEtaleTopology (ModuleCat.{u} (ZMod n))).obj
        (op (globalEtale X))).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((sheafSections X.smallEtaleTopology (ModuleCat.{u} (ZMod n))).obj
          (op (globalEtale X))))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))) (ComplexShape.up ℤ))]
    (I : Type u)
    [HasColimitsOfShape (Discrete I)
      (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))]
    [HasColimitsOfShape (Discrete I) (DerivedCategory (ModuleCat.{u} (ZMod n)))],
      PreservesColimitsOfShape (Discrete I)
        (RightDerived.Cochain.functor
          ((sheafSections X.smallEtaleTopology (ModuleCat.{u} (ZMod n))).obj
            (op (globalEtale X)))))

end AlgebraicGeometry.Scheme
