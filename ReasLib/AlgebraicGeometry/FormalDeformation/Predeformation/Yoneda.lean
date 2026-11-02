/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Map
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids

/-!
# Yoneda-induced predeformation morphisms

An object over a scheme determines a canonical morphism from the fibred slice by the
2-Yoneda construction, and hence a based functor between the associated predeformation
categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open FiberedCategoryOver.Groupoids (toFunctor fiberFunctor slice)
open FiberedCategoryOver.Groupoids.YonedaSlice

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

/-- The residue field `κ(u0)` of a point of a scheme `U`. -/
abbrev residueType {S : Scheme.{u}} (U : Over S) (u0 : U.left) : Type u :=
  IsLocalRing.ResidueField (U.left.presheaf.stalk u0)

/-- `residueType U u0` is the carrier of the residue field of `u0`. -/
theorem residueType_eq {S : Scheme.{u}} (U : Over S) (u0 : U.left) :
    residueType U u0 = U.left.residueField u0 := rfl

/-- The morphism `Spec κ(u0) ⟶ S` obtained by composing the canonical residue-field
point of `u0` with `U ⟶ S`. -/
abbrev residuePointToS {S : Scheme.{u}} (U : Over S) (u0 : U.left) :
    Spec (CommRingCat.of (residueType U u0)) ⟶ S :=
  U.left.fromSpecResidueField u0 ≫ U.hom

/-- `residuePointToS` is the composite of `fromSpecResidueField` with `U.hom`. -/
theorem residuePointToS_eq {S : Scheme.{u}} (U : Over S) (u0 : U.left) :
    residuePointToS U u0 = U.left.fromSpecResidueField u0 ≫ U.hom := rfl

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (U : Over S) (u0 : U.left)
variable [Algebra Λ (residueType U u0)]
variable [Module.Finite Λ (residueType U u0)]
variable (kToS : Spec (CommRingCat.of (residueType U u0)) ⟶ S)
variable [LocallyOfFiniteType kToS]
variable (h_factor :
    Spec.map (CommRingCat.ofHom (algebraMap Λ (residueType U u0))) ≫ openImmersion =
      kToS)
variable (h_kToS : kToS = residuePointToS U u0)
variable (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S))
variable (x : X.p.Fiber U)

/-- The object `u0` of `(Sch/U)_fppf` over the canonical residue-field point. -/
def residueFiber [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0] :
    (slice U).p.Fiber (Over.mk kToS) :=
  ⟨Over.mk (Over.homMk (U.left.fromSpecResidueField u0)
      h_kToS.symm : Over.mk kToS ⟶ U), rfl⟩

/-- `residueFiber` is the object of `Over U` given by the canonical residue-field
morphism of the finite type point. -/
theorem residueFiber_spec [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0] :
    Fiber.fiberInclusion.obj (residueFiber U u0 kToS h_kToS) =
      Over.mk (Over.homMk (U.left.fromSpecResidueField u0)
        h_kToS.symm : Over.mk kToS ⟶ U) := rfl

/-- The pullback `x0` of `x` along the canonical residue-field point of `u0`. -/
def residueObject [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0] :
    X.p.Fiber (Over.mk kToS) :=
  residueImage (representative x) (residueFiber U u0 kToS h_kToS)

/-- `residueObject` is the image of `residueFiber` under the fibre functor of the
2-Yoneda representative of `x`. -/
theorem residueObject_spec [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0] :
    residueObject U u0 kToS h_kToS X x =
      (fiberFunctor (representative x) (Over.mk kToS)).obj
        (residueFiber U u0 kToS h_kToS) := rfl

/-- The based functor induced by the 2-Yoneda representative of `x`. -/
def hat [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0] :
    predeformation openImmersion h_factor (slice U)
      (residueFiber U u0 kToS h_kToS) ⥤ᵇ
      predeformation openImmersion h_factor X
        (residueObject U u0 kToS h_kToS X x) :=
  map openImmersion h_factor (representative x) (residueFiber U u0 kToS h_kToS)

/-- Applying `hat` preserves the Artinian base and sends the target and residue morphism
along the 2-Yoneda representative of `x`. -/
theorem hat_obj [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0]
    (ξ : Obj openImmersion kToS h_factor (slice U)
      (residueFiber U u0 kToS h_kToS)) :
    ((hat openImmersion U u0 kToS h_factor h_kToS X x).obj ξ).base = ξ.base ∧
      ((hat openImmersion U u0 kToS h_factor h_kToS X x).obj ξ).target =
        (fiberFunctor (representative x) (specOver openImmersion ξ.base)).obj ξ.target ∧
      ((hat openImmersion U u0 kToS h_factor h_kToS X x).obj ξ).fromResidue =
        (toFunctor (representative x)).map ξ.fromResidue := ⟨rfl, rfl, rfl⟩

/-- Applying `hat` preserves the Artinian base homomorphism and sends the reversed
total-category arrow along the 2-Yoneda representative of `x`. -/
theorem hat_map [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0]
    {ξ η : Obj openImmersion kToS h_factor (slice U)
      (residueFiber U u0 kToS h_kToS)}
    (f : Hom ξ η) :
    ((hat openImmersion U u0 kToS h_factor h_kToS X x).map f).baseHom = f.baseHom ∧
      ((hat openImmersion U u0 kToS h_factor h_kToS X x).map f).hom =
        (toFunctor (representative x)).map f.hom := ⟨rfl, rfl⟩

/-- `hat` strictly commutes with the projections to Artinian local algebras. -/
theorem hat_w [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0] :
    (hat openImmersion U u0 kToS h_factor h_kToS X x).toFunctor ⋙
        forget openImmersion kToS h_factor X (residueObject U u0 kToS h_kToS X x) =
      forget openImmersion kToS h_factor (slice U)
        (residueFiber U u0 kToS h_kToS) := rfl

/-- `hat` is the predeformation functor induced by the 2-Yoneda representative of `x`. -/
theorem hat_spec [LocallyOfFiniteType U.hom] [IsFiniteTypePoint u0] :
    hat openImmersion U u0 kToS h_factor h_kToS X x =
      map openImmersion h_factor (representative x)
        (residueFiber U u0 kToS h_kToS) := rfl

end AlgebraicGeometry.GroupoidsOver.Predeformation
