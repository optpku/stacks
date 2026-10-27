/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Grothendieck.Cartesian
public import ReasLib.CategoryTheory.Sites.Simplicial.DerivedSystem

public section

open CategoryTheory CategoryTheory.Limits Opposite Functor

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [UnivLE.{max u v, w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

namespace AbelianDerived

/-- The family of abelian inverse-image functors is additive. -/
instance inverseImage_additive :
    ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ((abelianInverseImageExact F J φ).obj).Additive := sorry

/-- The family of abelian inverse-image functors preserves finite limits. -/
instance inverseImage_preservesFiniteLimits :
    ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      PreservesFiniteLimits (abelianInverseImageExact F J φ).obj := sorry

/-- The family of abelian inverse-image functors preserves finite colimits. -/
instance inverseImage_preservesFiniteColimits :
    ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      PreservesFiniteColimits (abelianInverseImageExact F J φ).obj := sorry

/-- Abelian cocontinuous inverse image is left adjoint to cocontinuous pushforward. -/
private def inverseImageAdjunction {m n : SimplexCategory} (φ : m ⟶ n) :
    (abelianInverseImageExact F J φ).obj ⊣
      (F.map φ.op).toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{w}
        (J (op n)).toGrothendieck (J (op m)).toGrothendieck :=
  (((F.map φ.op).toFunctor.op.ranAdjunction AddCommGrpCat.{w}).comp
    (sheafificationAdjunction (J (op n)).toGrothendieck AddCommGrpCat.{w})).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf (J (op m)).toGrothendieck AddCommGrpCat.{w})
    (Functor.FullyFaithful.id _) (Iso.refl _)
    ((F.map φ.op).toFunctor.sheafPushforwardCocontinuousCompSheafToPresheafIso
      AddCommGrpCat.{w} (J (op n)).toGrothendieck (J (op m)).toGrothendieck).symm

/-- Inverse image along a composite is canonically isomorphic to iterated inverse image. -/
def inverseImageCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (abelianInverseImageExact F J (ψ ≫ φ)).obj ≅
      (abelianInverseImageExact F J ψ).obj ⋙ (abelianInverseImageExact F J φ).obj :=
  (Adjunction.leftAdjointUniq
    (((inverseImageAdjunction F J ψ).comp (inverseImageAdjunction F J φ)).ofNatIsoRight
      (Functor.sheafPushforwardCocontinuousComp'
        (J (op n)).toGrothendieck (J (op m)).toGrothendieck (J (op l)).toGrothendieck
        (F.map φ.op).toFunctor (F.map ψ.op).toFunctor
        (A := AddCommGrpCat.{w}) (map_comp_toFunctor F ψ φ)))
    (inverseImageAdjunction F J (ψ ≫ φ))).symm

/-- The canonical cocontinuous pullbacks of a fiberwise site diagram form an
anchored inverse-image context with coherent unit and composition comparisons. -/
instance inverseImageContext :
    SimplicialSites.IsInverseImageContext (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ (abelianInverseImageExact F J φ).obj)
      (inverseImageCompIso F J) := sorry

end AbelianDerived

/-- Canonical derived restriction transitions respect composition of simplex operators. -/
theorem toDerivedSystem_map_comp
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    derivedTransition F J (ψ ≫ φ) K =
      (SimplicialSites.derivedInverseImageCompIso (fun n ↦ (J (op n)).toGrothendieck)
        (fun φ ↦ (abelianInverseImageExact F J φ).obj) ψ φ
        (AbelianDerived.inverseImageCompIso F J ψ φ)).hom.app ((derivedRestrict F J l).obj K) ≫
      ((abelianInverseImageExact F J φ).obj).mapDerivedCategory.map
        (derivedTransition F J ψ K) ≫ derivedTransition F J φ K := sorry

/-- An object of the total derived category determines its system of canonical restrictions. -/
@[expose] def toDerivedSystem (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})) :
    SimplicialSites.DerivedSystem (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ (abelianInverseImageExact F J φ).obj)
      (AbelianDerived.inverseImageCompIso F J) :=
  SimplicialSites.DerivedSystem.of inferInstance (fun n ↦ (derivedRestrict F J n).obj K)
    (fun φ ↦ derivedTransition F J φ K) (toDerivedSystem_map_comp F J K)

/-- The degree object of the restriction system is the canonical derived restriction. -/
theorem toDerivedSystem_obj
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})) (n : SimplexCategory) :
    (toDerivedSystem F J K).obj n = (derivedRestrict F J n).obj K := sorry

/-- The transition of the restriction system is the canonical derived comparison. -/
theorem toDerivedSystem_map
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (toDerivedSystem F J K).map φ = derivedTransition F J φ K := sorry

/-- The restriction system of a cartesian total derived object is cartesian. -/
theorem toDerivedSystem_isCartesian
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    [AbelianDerived.IsCartesian F J K] :
    SimplicialSites.DerivedSystem.IsCartesian (toDerivedSystem F J K) := sorry

end CategoryTheory.Grothendieck
