/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.ToUnbounded
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.InternalHom.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Dualizing.Basic

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
        ModuleDerived.InternalHom.sourceFunctor K.obj).obj L)) := sorry

/-- Derived internal Hom into `K`, restricted to complexes with coherent cohomology. -/
noncomputable def coherentDuality :
    (D[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ ⥤
      D[SheafOfModules.isCoherent (structureSheaf X)] :=
  (DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X))).lift
    ((DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X))).ι.op ⋙
      ModuleDerived.InternalHom.sourceFunctor K.obj)
    (coherentDualityObjMem K hK)

/-- The underlying object of `coherentDuality` is derived internal Hom into `K`. -/
theorem coherentDuality_obj_obj
    (L : (D[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ) :
    ((coherentDuality K hK).obj L).obj =
      ModuleDerived.InternalHom.obj (Opposite.unop L).obj K.obj := sorry

/-- Derived internal Hom into a dualizing complex is an anti-equivalence of complexes with coherent cohomology. -/
instance coherentDualityIsEquivalence :
    (coherentDuality K hK).IsEquivalence := sorry

/-- Naturality of the bidual map after restricting to complexes with coherent cohomology. -/
theorem coherentBidualNaturality
    {L M : D[SheafOfModules.isCoherent (structureSheaf X)]} (f : L ⟶ M) :
    f ≫ homMk (ModuleDerived.InternalHom.toBidualApp K.obj M.obj) =
      homMk (ModuleDerived.InternalHom.toBidualApp K.obj L.obj) ≫
        ((coherentDuality K hK).rightOp ⋙ coherentDuality K hK).map f := sorry

/-- The canonical bidual transformation on complexes with coherent cohomology. -/
noncomputable def coherentBidual :
    𝟭 (D[SheafOfModules.isCoherent (structureSheaf X)]) ⟶
      (coherentDuality K hK).rightOp ⋙ coherentDuality K hK where
  app L := homMk (ModuleDerived.InternalHom.toBidualApp K.obj L.obj)
  naturality _ _ f := coherentBidualNaturality K hK f

/-- The ambient component of `coherentBidual` is the canonical internal-Hom bidual map. -/
theorem coherentBidual_app_hom
    (L : D[SheafOfModules.isCoherent (structureSheaf X)]) :
    ((coherentBidual K hK).app L).hom =
      ModuleDerived.InternalHom.toBidualApp K.obj L.obj := sorry

/-- The canonical bidual transformation is an isomorphism. -/
instance coherentBidualIsIso : IsIso (coherentBidual K hK) := sorry

section PlusDuality
variable [IsQuasiCompact X]
open DerivedCategory.Plus.CohomologyIn

/-- Derived internal Hom into a dualizing complex sends bounded-below coherent complexes to bounded-above complexes. -/
theorem plusDualityObjBoundedAbove
    (L : (D⁺[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ) :
    (t.minus : ObjectProperty (ModuleDerived X))
      ((((ambient (SheafOfModules.isCoherent (structureSheaf X))).op ⋙
        ModuleDerived.InternalHom.sourceFunctor K.obj).obj L)) := sorry

/-- The bounded-above image of a bounded-below coherent complex has coherent cohomology. -/
theorem plusDualityObjCoherent
    (L : (D⁺[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ) :
    DerivedCategory.Minus.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X))
      (((t.minus : ObjectProperty (ModuleDerived X)).lift
        ((ambient (SheafOfModules.isCoherent (structureSheaf X))).op ⋙
          ModuleDerived.InternalHom.sourceFunctor K.obj)
        (plusDualityObjBoundedAbove K hK)).obj L) := sorry

/-- Derived internal Hom into `K`, from bounded-below to bounded-above coherent complexes. -/
noncomputable def plusDuality :
    (D⁺[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ ⥤
      D⁻[SheafOfModules.isCoherent (structureSheaf X)] :=
  (DerivedCategory.Minus.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X))).lift
    ((t.minus : ObjectProperty (ModuleDerived X)).lift
      ((ambient (SheafOfModules.isCoherent (structureSheaf X))).op ⋙
        ModuleDerived.InternalHom.sourceFunctor K.obj)
      (plusDualityObjBoundedAbove K hK))
    (plusDualityObjCoherent K hK)

/-- The ambient value of `plusDuality` is derived internal Hom into `K`. -/
theorem plusDuality_obj_obj_obj
    (L : (D⁺[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ) :
    ((plusDuality K hK).obj L).obj.obj =
      ModuleDerived.InternalHom.obj (Opposite.unop L).obj.obj K.obj := sorry

/-- On a quasi-compact algebraic space, this duality exchanges bounded-below and bounded-above coherent complexes. -/
instance plusDualityIsEquivalence :
    (plusDuality K hK).IsEquivalence := sorry
end PlusDuality

section BoundedDuality
variable [IsQuasiCompact X]
open DerivedCategory.Bounded.CohomologyIn

/-- Derived internal Hom into a dualizing complex preserves bounded complexes. -/
theorem boundedDualityObjBounded
    (L : (Dᵇ[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ) :
    (t.bounded : ObjectProperty (ModuleDerived X))
      ((((ambient (SheafOfModules.isCoherent (structureSheaf X))).op ⋙
        ModuleDerived.InternalHom.sourceFunctor K.obj).obj L)) := sorry

/-- The bounded image of a bounded coherent complex still has coherent cohomology. -/
theorem boundedDualityObjCoherent
    (L : (Dᵇ[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ) :
    DerivedCategory.Bounded.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X))
      (((t.bounded : ObjectProperty (ModuleDerived X)).lift
        ((ambient (SheafOfModules.isCoherent (structureSheaf X))).op ⋙
          ModuleDerived.InternalHom.sourceFunctor K.obj)
        (boundedDualityObjBounded K hK)).obj L) := sorry

/-- Derived internal Hom into `K`, restricted to bounded complexes with coherent cohomology. -/
noncomputable def boundedDuality :
    (Dᵇ[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ ⥤
      Dᵇ[SheafOfModules.isCoherent (structureSheaf X)] :=
  (DerivedCategory.Bounded.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X))).lift
    ((t.bounded : ObjectProperty (ModuleDerived X)).lift
      ((ambient (SheafOfModules.isCoherent (structureSheaf X))).op ⋙
        ModuleDerived.InternalHom.sourceFunctor K.obj)
      (boundedDualityObjBounded K hK))
    (boundedDualityObjCoherent K hK)

/-- The ambient value of `boundedDuality` is derived internal Hom into `K`. -/
theorem boundedDuality_obj_obj_obj
    (L : (Dᵇ[SheafOfModules.isCoherent (structureSheaf X)])ᵒᵖ) :
    ((boundedDuality K hK).obj L).obj.obj =
      ModuleDerived.InternalHom.obj (Opposite.unop L).obj.obj K.obj := sorry

/-- On a quasi-compact algebraic space, this duality is an anti-equivalence on bounded coherent complexes. -/
instance boundedDualityIsEquivalence :
    (boundedDuality K hK).IsEquivalence := sorry
end BoundedDuality
end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex
