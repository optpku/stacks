module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.ToUnbounded
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Bidual
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap86.Definition_86_2_2_DualizingComplex

/-!
# Duality for dualizing complexes on algebraic spaces

Derived internal Hom into a dualizing complex on a locally Noetherian algebraic space
restricts to an anti-equivalence of complexes with coherent cohomology, equipped with the
canonical bidual isomorphism. On a quasi-compact algebraic space it exchanges bounded-below
and bounded-above coherent complexes and restricts to bounded coherent complexes.
-/

@[expose] public section
open CategoryTheory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open DerivedCategory.TStructure
open scoped DerivedCategory.CohomologyIn
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex
variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
variable [MonoidalCategory (ModuleDerived X)]
variable [BraidedCategory (ModuleDerived X)]
variable (H : MonoidalClosed (ModuleDerived X))
variable (K : DerivedQCoh X)
variable (hK : IsDualizingComplex K)
include hK

/-- The cohomology of a dualizing complex is coherent. -/
theorem coherentCohomology :
    DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) K.obj := sorry

/-- Derived internal Hom into a dualizing complex preserves coherent cohomology. -/
theorem coherentDualityObjMem
    (L : (D[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ) :
    DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X))
      ((((DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent (structureSheaf X))).ι.op ⋙
        (RightInternalHom.ofBraidedClosedOf H).dualFunctor K.obj).obj L)) := sorry

/-- Derived internal Hom into `K`, restricted to complexes with coherent cohomology. -/
noncomputable def coherentDuality :
    (D[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ ⥤
      D[SheafOfModules.isCoherent (structureSheaf X)] :=
  (DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X))).lift
    ((DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X))).ι.op ⋙
      (RightInternalHom.ofBraidedClosedOf H).dualFunctor K.obj)
    (coherentDualityObjMem H K hK)

/-- The underlying object of `coherentDuality` is derived internal Hom into `K`. -/
theorem coherentDuality_obj_obj
    (L : (D[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ) :
    ((coherentDuality H K hK).obj L).obj =
      (MonoidalClosed.ihomOf H (Opposite.unop L).obj).obj K.obj := sorry

/-- Derived internal Hom into a dualizing complex is an anti-equivalence of complexes with coherent cohomology. -/
theorem coherentDualityIsEquivalence :
    (coherentDuality H K hK).IsEquivalence := sorry

/-- Naturality of the bidual map after restricting to complexes with coherent cohomology. -/
theorem coherentBidualNaturality
    {L M : D[SheafOfModules.isCoherent (structureSheaf X)]} (f : L ⟶ M) :
    f ≫ homMk ((RightInternalHom.ofBraidedClosedOf H).toBidualApp K.obj M.obj) =
      homMk ((RightInternalHom.ofBraidedClosedOf H).toBidualApp K.obj L.obj) ≫
        ((coherentDuality H K hK).rightOp ⋙ coherentDuality H K hK).map f := sorry

/-- The canonical bidual transformation on complexes with coherent cohomology. -/
noncomputable def coherentBidual :
    𝟭 (D[SheafOfModules.isCoherent (structureSheaf X)]) ⟶
      (coherentDuality H K hK).rightOp ⋙ coherentDuality H K hK where
  app L := homMk ((RightInternalHom.ofBraidedClosedOf H).toBidualApp K.obj L.obj)
  naturality _ _ f := coherentBidualNaturality H K hK f

/-- The ambient component of `coherentBidual` is the canonical internal-Hom bidual map. -/
theorem coherentBidual_app_hom
    (L : D[SheafOfModules.isCoherent (structureSheaf X)]) :
    ((coherentBidual H K hK).app L).hom =
      (RightInternalHom.ofBraidedClosedOf H).toBidualApp K.obj L.obj := sorry

/-- The canonical bidual transformation is an isomorphism. -/
theorem coherentBidualIsIso : IsIso (coherentBidual H K hK) := sorry

section PlusDuality
variable [IsQuasiCompact X]
open DerivedCategory.Plus.CohomologyIn

/-- Derived internal Hom into a dualizing complex sends bounded-below coherent complexes to bounded-above complexes. -/
theorem plusDualityObjBoundedAbove
    (L : (D⁺[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ) :
    (t.minus : ObjectProperty (ModuleDerived X))
      ((((ambient (SheafOfModules.isCoherent (structureSheaf X))).op ⋙
        (RightInternalHom.ofBraidedClosedOf H).dualFunctor K.obj).obj L)) := sorry

/-- The bounded-above image of a bounded-below coherent complex has coherent cohomology. -/
theorem plusDualityObjCoherent
    (L : (D⁺[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ) :
    DerivedCategory.Minus.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X))
      (((t.minus : ObjectProperty (ModuleDerived X)).lift
        ((ambient (SheafOfModules.isCoherent (structureSheaf X))).op ⋙
          (RightInternalHom.ofBraidedClosedOf H).dualFunctor K.obj)
        (plusDualityObjBoundedAbove H K hK)).obj L) := sorry

/-- Derived internal Hom into `K`, from bounded-below to bounded-above coherent complexes. -/
noncomputable def plusDuality :
    (D⁺[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ ⥤
      D⁻[SheafOfModules.isCoherent (structureSheaf X)] :=
  (DerivedCategory.Minus.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X))).lift
    ((t.minus : ObjectProperty (ModuleDerived X)).lift
      ((ambient (SheafOfModules.isCoherent (structureSheaf X))).op ⋙
        (RightInternalHom.ofBraidedClosedOf H).dualFunctor K.obj)
      (plusDualityObjBoundedAbove H K hK))
    (plusDualityObjCoherent H K hK)

/-- The ambient value of `plusDuality` is derived internal Hom into `K`. -/
theorem plusDuality_obj_obj_obj
    (L : (D⁺[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ) :
    ((plusDuality H K hK).obj L).obj.obj =
      (MonoidalClosed.ihomOf H (Opposite.unop L).obj.obj).obj K.obj := sorry

/-- On a quasi-compact algebraic space, this duality exchanges bounded-below and bounded-above coherent complexes. -/
theorem plusDualityIsEquivalence :
    (plusDuality H K hK).IsEquivalence := sorry
end PlusDuality

section BoundedDuality
variable [IsQuasiCompact X]
open DerivedCategory.Bounded.CohomologyIn

/-- Derived internal Hom into a dualizing complex preserves bounded complexes. -/
theorem boundedDualityObjBounded
    (L : (Dᵇ[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ) :
    (t.bounded : ObjectProperty (ModuleDerived X))
      ((((ambient (SheafOfModules.isCoherent (structureSheaf X))).op ⋙
        (RightInternalHom.ofBraidedClosedOf H).dualFunctor K.obj).obj L)) := sorry

/-- The bounded image of a bounded coherent complex still has coherent cohomology. -/
theorem boundedDualityObjCoherent
    (L : (Dᵇ[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ) :
    DerivedCategory.Bounded.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X))
      (((t.bounded : ObjectProperty (ModuleDerived X)).lift
        ((ambient (SheafOfModules.isCoherent (structureSheaf X))).op ⋙
          (RightInternalHom.ofBraidedClosedOf H).dualFunctor K.obj)
        (boundedDualityObjBounded H K hK)).obj L) := sorry

/-- Derived internal Hom into `K`, restricted to bounded complexes with coherent cohomology. -/
noncomputable def boundedDuality :
    (Dᵇ[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ ⥤
      Dᵇ[SheafOfModules.isCoherent (structureSheaf X)] :=
  (DerivedCategory.Bounded.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X))).lift
    ((t.bounded : ObjectProperty (ModuleDerived X)).lift
      ((ambient (SheafOfModules.isCoherent (structureSheaf X))).op ⋙
        (RightInternalHom.ofBraidedClosedOf H).dualFunctor K.obj)
      (boundedDualityObjBounded H K hK))
    (boundedDualityObjCoherent H K hK)

/-- The ambient value of `boundedDuality` is derived internal Hom into `K`. -/
theorem boundedDuality_obj_obj_obj
    (L : (Dᵇ[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ) :
    ((boundedDuality H K hK).obj L).obj.obj =
      (MonoidalClosed.ihomOf H (Opposite.unop L).obj.obj).obj K.obj := sorry

/-- On a quasi-compact algebraic space, this duality is an anti-equivalence on bounded coherent complexes. -/
theorem boundedDualityIsEquivalence :
    (boundedDuality H K hK).IsEquivalence := sorry
end BoundedDuality
end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex
