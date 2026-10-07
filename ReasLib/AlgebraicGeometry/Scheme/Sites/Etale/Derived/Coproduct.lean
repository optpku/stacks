module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.CohomologicalDimension
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CohomologicalDimension
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Coproducts
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Coproducts of derived étale sections
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open scoped GrothendieckTopologyDerivedSections
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X)))
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
variable {I : Type u}
variable (K : I → DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
variable [HasCoproductsOfShape I (DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
variable [HasCoproductsOfShape I (DerivedCategory AddCommGrpCat.{u})]

/-- For a quasi-compact, quasi-separated scheme, derived étale sections commute with coproducts of
a uniformly bounded-below family of derived objects. -/
theorem etaleDerivedSections_preservesCoproduct (a : ℤ) (hK : ∀ i : I, (K i).IsGE a) :
    IsIso
      (sigmaComparison (siteAbelianSectionsDerived X.smallEtaleTopology (globalEtale X)) K) := sorry

/-- The homology map induced by the derived sections coproduct comparison is an isomorphism in
every integer degree. -/
theorem etaleDerivedSections_preservesCoproduct_homology
    (a : ℤ) (hK : ∀ i : I, (K i).IsGE a) (p : ℤ)
    [HasCoproductsOfShape I AddCommGrpCat.{u}] :
    IsIso
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} p).map
        (sigmaComparison (siteAbelianSectionsDerived X.smallEtaleTopology (globalEtale X)) K)) := sorry

end AlgebraicGeometry.Scheme.Etale

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}}

/-- For a quasi-compact, quasi-separated morphism of schemes with finite étale cohomological
dimension and positive coefficient modulus, derived étale direct image preserves coproducts. -/
theorem directImage_preservesCoproducts_of_finiteCohomologicalDimension
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (n : ℕ) (hn : 0 < n)
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
      (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))))] :
    PreservesColimitsOfShape (Discrete I)
      (RightDerived.Cochain.functor
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} (ZMod n)) Y.smallEtaleTopology X.smallEtaleTopology)) := sorry

/-- For a quasi-compact, quasi-separated scheme with finite étale cohomological dimension and
positive coefficient modulus, derived étale global sections preserve coproducts. -/
theorem sections_preservesCoproducts_of_finiteCohomologicalDimension
    [CompactSpace X] [QuasiSeparatedSpace X] (n : ℕ) (hn : 0 < n)
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
    [HasColimitsOfShape (Discrete I) (DerivedCategory (ModuleCat.{u} (ZMod n)))] :
    PreservesColimitsOfShape (Discrete I)
      (RightDerived.Cochain.functor
        ((sheafSections X.smallEtaleTopology (ModuleCat.{u} (ZMod n))).obj
          (op (globalEtale X)))) := sorry

end AlgebraicGeometry.Scheme.Etale

end
