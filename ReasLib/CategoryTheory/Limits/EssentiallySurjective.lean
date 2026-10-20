/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Products and Coproducts Transported by Essentially Surjective Functors

An essentially surjective functor transports a product or coproduct to its target once it
preserves the corresponding discrete (co)limit of chosen object preimages.  This leaf exposes
the chosen preimage family, the comparison of diagrams, and the resulting concrete fan or cofan
before registering shape-wide instances.
-/

@[expose] public section

noncomputable section

universe uC vC uD vD w

open CategoryTheory.Limits

namespace CategoryTheory.Functor.EssSurj

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable (F : C ⥤ D) [F.EssSurj]

/-- A chosen family of source objects representing a family in the target of an essentially
surjective functor. -/
abbrev preimageFamily {J : Type w} (X : J → D) : J → C :=
  fun j ↦ F.objPreimage (X j)

/-- The images of the chosen object preimages form a discrete diagram canonically isomorphic
to the original target family. -/
noncomputable def preimageDiagramIso {J : Type w} (X : J → D) :
    Discrete.functor (fun j ↦ F.obj (preimageFamily F X j)) ≅ Discrete.functor X :=
  Discrete.natIso fun j ↦ F.objObjPreimageIso (X j.as)

/-- The fan obtained by applying an essentially surjective functor to a product of chosen
object preimages and transporting its legs to the original target family. -/
noncomputable def productFan {J : Type w} (X : J → D)
    [HasProduct (preimageFamily F X)] : Fan X :=
  (Cone.postcompose (preimageDiagramIso F X).hom).obj
    (Fan.mk (F.obj (∏ᶜ (preimageFamily F X)))
      (fun j ↦ F.map (Pi.π (preimageFamily F X) j)))

/-- If the functor preserves the product of the chosen preimages, the transported fan is a
product fan for the original target family. -/
noncomputable def productFanIsLimit {J : Type w} (X : J → D)
    [HasProduct (preimageFamily F X)]
    [PreservesLimit (Discrete.functor (preimageFamily F X)) F] :
    IsLimit (productFan F X) :=
  (IsLimit.postcomposeHomEquiv
    (preimageDiagramIso F X)
    (Fan.mk (F.obj (∏ᶜ (preimageFamily F X)))
      (fun j ↦ F.map (Pi.π (preimageFamily F X) j)))).invFun
    (isLimitOfHasProductOfPreservesLimit F (preimageFamily F X))

/-- The explicit limit cone in the target obtained from preserved products of chosen
preimages. -/
noncomputable def productLimitCone {J : Type w} (X : J → D)
    [HasProduct (preimageFamily F X)]
  [PreservesLimit (Discrete.functor (preimageFamily F X)) F] :
    LimitCone (Discrete.functor X) where
  cone := productFan F X
  isLimit := productFanIsLimit F X

set_option linter.defProp false in
/-- An essentially surjective functor transfers products of shape `J` when it preserves the
products of the chosen object preimages. -/
@[reducible]
noncomputable def hasProductsOfShape {J : Type w}
    [HasProductsOfShape J C]
    [∀ X : J → D, PreservesLimit (Discrete.functor (preimageFamily F X)) F] :
    HasProductsOfShape J D where
  has_limit K := HasLimit.mk
    ⟨(Cone.postcompose Discrete.natIsoFunctor.inv).obj
        (productFan F (fun j ↦ K.obj ⟨j⟩)),
      (IsLimit.postcomposeInvEquiv _ _).symm
        (productFanIsLimit F (fun j ↦ K.obj ⟨j⟩))⟩

/-- The cofan obtained by applying an essentially surjective functor to a coproduct of chosen
object preimages and transporting its legs to the original target family. -/
noncomputable def coproductCofan {J : Type w} (X : J → D)
    [HasCoproduct (preimageFamily F X)] : Cofan X :=
  (Cocone.precompose (preimageDiagramIso F X).inv).obj
    (Cofan.mk (F.obj (∐ (preimageFamily F X)))
      (fun j ↦ F.map (Sigma.ι (preimageFamily F X) j)))

/-- If the functor preserves the coproduct of the chosen preimages, the transported cofan is a
coproduct cofan for the original target family. -/
noncomputable def coproductCofanIsColimit {J : Type w} (X : J → D)
    [HasCoproduct (preimageFamily F X)]
    [PreservesColimit (Discrete.functor (preimageFamily F X)) F] :
    IsColimit (coproductCofan F X) :=
  (IsColimit.precomposeInvEquiv
    (preimageDiagramIso F X)
    (Cofan.mk (F.obj (∐ (preimageFamily F X)))
      (fun j ↦ F.map (Sigma.ι (preimageFamily F X) j)))).symm
    (isColimitOfHasCoproductOfPreservesColimit F (preimageFamily F X))

/-- The explicit colimit cocone in the target obtained from preserved coproducts of chosen
preimages. -/
noncomputable def coproductColimitCocone {J : Type w} (X : J → D)
    [HasCoproduct (preimageFamily F X)]
  [PreservesColimit (Discrete.functor (preimageFamily F X)) F] :
    ColimitCocone (Discrete.functor X) where
  cocone := coproductCofan F X
  isColimit := coproductCofanIsColimit F X

set_option linter.defProp false in
/-- An essentially surjective functor transfers coproducts of shape `J` when it preserves the
coproducts of the chosen object preimages. -/
@[reducible]
noncomputable def hasCoproductsOfShape {J : Type w}
    [HasCoproductsOfShape J C]
    [∀ X : J → D, PreservesColimit (Discrete.functor (preimageFamily F X)) F] :
    HasCoproductsOfShape J D where
  has_colimit K := HasColimit.mk
    ⟨(Cocone.precompose Discrete.natIsoFunctor.hom).obj
        (coproductCofan F (fun j ↦ K.obj ⟨j⟩)),
      (IsColimit.precomposeHomEquiv _ _).symm
        (coproductCofanIsColimit F (fun j ↦ K.obj ⟨j⟩))⟩

end CategoryTheory.Functor.EssSurj
