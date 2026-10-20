/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Unit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed comparison for the canonical RHom unit

This leaf is the bundled bridge from a closed presentation of canonical module `RHom` to the
minimal unit API.  The underlying degree-zero object, scalar action, tensor-unit comparison, and
single-adjunction transport remain in the lighter `RHom.Unit` owner.
@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.MonoidalCategory

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.Unit

variable {A : Type u} [CommRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat A))]
variable [RHom.Has (A := A)]

/-- 0E1U: The canonical `RHom(A[0], -)` unit isomorphism obtained from a bundled closed comparison and
an explicit identification of `A[0]` with its tensor unit. -/
@[stacks 0E1U "bundled canonical RHom unit comparison"]
noncomputable def targetIso
    (M : RHom.ClosedComparison (A := A))
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat A))) :
    RHom.targetFunctor (A := A) (single (A := A)) ≅
      𝟭 (DerivedCategory (ModuleCat A)) :=
  targetIsoOf (A := A) (M.adjunction (single (A := A)))
    (tensorUnitComparisonOf (A := A) M.tensorModel s)

/-- 0E1U: The objectwise bundled comparison `RHom_A(A[0], K) ≅ K`. -/
@[stacks 0E1U "bundled canonical RHom unit object comparison"]
noncomputable abbrev objIso
    (M : RHom.ClosedComparison (A := A))
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat A)))
    (K : DerivedCategory (ModuleCat A)) :
    RHom.obj (A := A) (single (A := A)) K ≅ K :=
  (targetIso (A := A) M s).app K

/-- 0E1U: The bundled canonical unit comparison is natural in its target. -/
@[reassoc, stacks 0E1U "bundled canonical RHom unit naturality"]
theorem objIso_naturality
    (M : RHom.ClosedComparison (A := A))
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat A)))
    {K L : DerivedCategory (ModuleCat A)} (f : K ⟶ L) :
    (RHom.targetFunctor (A := A) (single (A := A))).map f ≫
        (objIso (A := A) M s L).hom =
      (objIso (A := A) M s K).hom ≫ f :=
  objIsoOf_naturality (A := A) (M.adjunction (single (A := A)))
    (tensorUnitComparisonOf (A := A) M.tensorModel s) f

/-- 0E1U: Under the bundled unit comparison, regular-source precomposition becomes scalar
multiplication on the target object. -/
@[reassoc, stacks 0E1U "bundled regular RHom scalar comparison"]
theorem singlePre_objIso_hom
    (M : RHom.ClosedComparison (A := A))
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat A)))
    (a : A) (K : DerivedCategory (ModuleCat A)) :
    (singlePre (A := A) a).app K ≫ (objIso (A := A) M s K).hom =
      (objIso (A := A) M s K).hom ≫ (a • 𝟙 K) :=
  singlePre_objIsoOf_hom (A := A) (M.adjunction (single (A := A)))
    (tensorUnitComparisonOf (A := A) M.tensorModel s) a K

/-- The canonical `RHom` unit induced by a map from its source to the regular degree-zero
object. -/
@[stacks 0E1U "regular-source canonical RHom precomposition unit"]
noncomputable def unitOfPre
    (M : RHom.ClosedComparison (A := A))
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat A)))
    {X : DerivedCategory (ModuleCat A)} (p : X ⟶ single (A := A)) :
    𝟭 (DerivedCategory (ModuleCat A)) ⟶ RHom.targetFunctor (A := A) X :=
  RHom.unitOfPre (targetIso (A := A) M s) p

/-- The regular-source wrapper is the explicit-unit canonical `RHom` construction. -/
@[simp, stacks 0E1U "regular-source RHom unit canonical formula"]
theorem unitOfPre_eq_rhom
    (M : RHom.ClosedComparison (A := A))
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat A)))
    {X : DerivedCategory (ModuleCat A)} (p : X ⟶ single (A := A)) :
    unitOfPre M s p = RHom.unitOfPre (targetIso (A := A) M s) p := rfl

/-- Objectwise, the canonical unit induced by `p` is the inverse regular-source unit comparison
followed by canonical `RHom` precomposition along `p`. -/
@[simp, stacks 0E1U "regular-source RHom unit component"]
theorem unitOfPre_app
    (M : RHom.ClosedComparison (A := A))
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat A)))
    {X : DerivedCategory (ModuleCat A)} (p : X ⟶ single (A := A))
    (K : DerivedCategory (ModuleCat A)) :
    (unitOfPre M s p).app K =
      (objIso (A := A) M s K).inv ≫ (RHom.pre (A := A) p).app K :=
  RHom.unitOfPre_app (targetIso (A := A) M s) p K

/-- The canonical `RHom` unit induced by precomposition is natural in its target object. -/
@[reassoc, stacks 0E1U "regular-source RHom unit naturality"]
theorem unitOfPre_naturality
    (M : RHom.ClosedComparison (A := A))
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat A)))
    {X K L : DerivedCategory (ModuleCat A)}
    (p : X ⟶ single (A := A)) (f : K ⟶ L) :
    f ≫ (unitOfPre M s p).app L =
      (unitOfPre M s p).app K ≫ (RHom.targetFunctor (A := A) X).map f :=
  RHom.unitOfPre_naturality (targetIso (A := A) M s) p f

/-- Precomposing the source map of a canonical `RHom` unit composes that unit with canonical
`RHom` precomposition. -/
@[stacks 0E1U "regular-source RHom unit composition"]
theorem unitOfPre_comp
    (M : RHom.ClosedComparison (A := A))
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat A)))
    {X Y : DerivedCategory (ModuleCat A)}
    (p : X ⟶ single (A := A)) (q : Y ⟶ X) :
    unitOfPre M s (q ≫ p) = unitOfPre M s p ≫ RHom.pre (A := A) q :=
  RHom.unitOfPre_comp (targetIso (A := A) M s) p q

/-- The canonical `RHom` unit induced by the identity of the regular degree-zero object is the
inverse regular-source unit comparison. -/
@[simp, stacks 0E1U "regular-source RHom unit identity"]
theorem unitOfPre_id
    (M : RHom.ClosedComparison (A := A))
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat A))) :
    unitOfPre M s (𝟙 (single (A := A))) = (targetIso (A := A) M s).inv :=
  RHom.unitOfPre_id (single (A := A)) (targetIso (A := A) M s)

/-- The canonical unit induced by multiplication on the regular degree-zero object is scalar
multiplication followed by the inverse regular-source unit comparison. -/
@[simp, stacks 0E1U "regular-source RHom scalar unit component"]
theorem unitOfPre_singleMap_app
    (M : RHom.ClosedComparison (A := A))
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat A)))
    (a : A) (K : DerivedCategory (ModuleCat A)) :
    (unitOfPre M s (singleMap (A := A) a)).app K =
      (a • 𝟙 K) ≫ (objIso (A := A) M s K).inv := by
  rw [unitOfPre_app]
  apply (cancel_mono (objIso (A := A) M s K).hom).1
  change
    ((objIso (A := A) M s K).inv ≫ (singlePre (A := A) a).app K) ≫
        (objIso (A := A) M s K).hom =
      ((a • 𝟙 K) ≫ (objIso (A := A) M s K).inv) ≫
        (objIso (A := A) M s K).hom
  simp only [Category.assoc]
  rw [singlePre_objIso_hom]
  simp

section Selected

variable [BraidedCategory (DerivedCategory (ModuleCat A))]

/-- A selected closed internal-Hom unit comparison obtained by explicitly transporting the
canonical `RHom` unit through the bundled closed comparison. -/
@[stacks 0E1U "selected internal-Hom unit comparison"]
noncomputable def ihomTargetIso
    (M : RHom.ClosedComparison (A := A))
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat A))) :
    MonoidalClosed.ihomOf M.closed (single (A := A)) ≅
      𝟭 (DerivedCategory (ModuleCat A)) :=
  (RHom.ClosedComparison.targetIso M (single (A := A))).symm ≪≫
    targetIso (A := A) M s

/-- The objectwise selected internal-Hom unit comparison. -/
@[stacks 0E1U "selected internal-Hom unit object comparison"]
noncomputable abbrev ihomObjIso
    (M : RHom.ClosedComparison (A := A))
    (s : single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat A)))
    (K : DerivedCategory (ModuleCat A)) :
    (MonoidalClosed.ihomOf M.closed (single (A := A))).obj K ≅ K :=
  (ihomTargetIso (A := A) M s).app K

end Selected

end CategoryTheory.DerivedCategory.InternalHom.RHom.Unit
