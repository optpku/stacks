/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientPresheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf

/-!
# Quotient sheaves of pre-relations on algebraic spaces

The quotient sheaf of a pre-relation is the fppf sheafification of its objectwise
quotient presheaf, together with the canonical map from the sheaf of points of the
ambient algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- The fppf quotient sheaf `U/R` of a pre-relation, obtained by sheafifying the
universe-raised objectwise quotient presheaf. -/
noncomputable def quotientSheaf {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj
    (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})

/-- The underlying presheaf of `quotientSheaf` is the sheafification of the universe-raised
quotient presheaf. -/
theorem quotientSheaf_val {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    (P.quotientSheaf).obj =
      sheafify (Scheme.fppfTopology.over S)
        (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}) :=
  rfl

/-- The section of the quotient sheaf represented by a scheme-valued point of `U`. -/
noncomputable def quotientClass {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) (T : Over S) (a : U.left.functorOfPoints.obj (op T)) :
    P.quotientSheaf.obj.obj (op T) :=
  (toSheafify (Scheme.fppfTopology.over S)
    (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})).app (op T)
      (ULift.up (Quot.mk (P.schemePointRel T) a))

/-- A quotient section is the image of its universe-raised quotient class under the
sheafification unit. -/
theorem quotientClass_def {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) (T : Over S) (a : U.left.functorOfPoints.obj (op T)) :
    P.quotientClass T a =
      (toSheafify (Scheme.fppfTopology.over S)
        (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})).app (op T)
          (ULift.up (Quot.mk (P.schemePointRel T) a)) := rfl

/-- The canonical morphism `U ⟶ U/R` of fppf sheaves. -/
noncomputable def quotientMap {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    toSheaf.obj U.left ⟶ P.quotientSheaf :=
  Sheaf.homEquiv.symm
    (Functor.whiskerRight P.quotientMk uliftFunctor.{u + 1, u} ≫
      toSheafify (Scheme.fppfTopology.over S)
        (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}))

/-- The quotient map equalizes the source and target projections of the pre-relation. -/
theorem quotientMap_s_eq_t {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    toSheaf.map P.t.left ≫ P.quotientMap =
      toSheaf.map P.s.left ≫ P.quotientMap := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.ext_apply
  intro r
  change (toSheafify (Scheme.fppfTopology.over S)
      (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})).app T
        (ULift.up (Quot.mk (P.schemePointRel T.unop) (P.t.left.app T r.down))) =
    (toSheafify (Scheme.fppfTopology.over S)
      (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})).app T
        (ULift.up (Quot.mk (P.schemePointRel T.unop) (P.s.left.app T r.down)))
  exact congrArg (fun q ↦ (toSheafify (Scheme.fppfTopology.over S)
    (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})).app T (ULift.up q))
      (Quot.sound ⟨r.down, rfl, rfl⟩)

/-- The canonical morphism from the quotient sheaf to the sheaf of points of the base. -/
noncomputable def toBaseSheaf {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) : P.quotientSheaf ⟶ toSheaf.obj B :=
  ((sheafificationAdjunction (Scheme.fppfTopology.over S) (Type (u + 1))).homEquiv
    (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}) (toSheaf.obj B)).symm
      (Functor.whiskerRight P.toBase uliftFunctor.{u + 1, u})

/-- Composing the sheafification unit with the descended base map gives the
universe-raised transformation from the quotient presheaf to the base. -/
theorem toBaseSheaf_hom {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    toSheafify (Scheme.fppfTopology.over S)
        (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}) ≫ P.toBaseSheaf.hom =
      Functor.whiskerRight P.toBase uliftFunctor.{u + 1, u} := by
  exact ((sheafificationAdjunction (Scheme.fppfTopology.over S) (Type (u + 1))).homEquiv
    (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}) (toSheaf.obj B)).apply_symm_apply _

/-- Restricting a quotient class along a morphism of schemes over `S` gives the quotient
class of the restricted point. -/
theorem quotientClass_map {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) {T T' : Over S} (f : T' ⟶ T)
    (a : U.left.functorOfPoints.obj (op T)) :
    P.quotientSheaf.obj.map f.op (P.quotientClass T a) =
      P.quotientClass T' (U.left.functorOfPoints.map f.op a) := by
  exact (NatTrans.naturality_apply (CD := fun X : Type (u + 1) ↦ X)
    (toSheafify (Scheme.fppfTopology.over S)
      (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})) f.op
        (ULift.up (Quot.mk (P.schemePointRel T) a))).symm

/-- The canonical morphism of fppf sheaves `R ⟶ U ×_{U/R} U` is the lift of the
universe-raised source and target maps through the kernel pair of the quotient map. -/
noncomputable def relationToKernelPair {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} (P : PreRelation U) :
    toSheaf.obj P.left.left ⟶ pullback P.quotientMap P.quotientMap :=
  pullback.lift (toSheaf.map P.s.left) (toSheaf.map P.t.left) P.quotientMap_s_eq_t.symm

/-- The first projection of the kernel-pair comparison is the universe-raised source map. -/
theorem relationToKernelPair_fst {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    P.relationToKernelPair ≫ pullback.fst P.quotientMap P.quotientMap =
      toSheaf.map P.s.left := by
  exact pullback.lift_fst _ _ _

/-- The second projection of the kernel-pair comparison is the universe-raised target map. -/
theorem relationToKernelPair_snd {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    P.relationToKernelPair ≫ pullback.snd P.quotientMap P.quotientMap =
      toSheaf.map P.t.left := by
  exact pullback.lift_snd _ _ _

end AlgebraicGeometry.AlgebraicSpace.PreRelation
