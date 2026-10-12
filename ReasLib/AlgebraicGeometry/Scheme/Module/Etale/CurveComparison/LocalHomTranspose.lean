/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommLocalHomEvaluation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommLocalHomCoefficient

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace LocalHomTranspose
variable {A R : Type (u + 1)} [CommRing A] [Ring R]
variable (h : A →+* R) (hc : ∀ (a : A) (r : R), h a * r = r * h a)
variable (Y : Scheme.{u})
variable [Y.smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable [Y.smallEtaleTopology.HasSheafCompose
  (NoncommLocalHom.modules (NoncommLocalHom.opScalarHom h hc))]
variable [Y.smallEtaleTopology.HasSheafCompose
  (ModuleCat.restrictScalars (RingEquiv.opOp R).toRingHom)]
variable (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
variable (B : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ))
variable (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
variable (e : B ⟶ NoncommLocalHom.obj h hc Y F J)

/-- Remove only the double opposite after the SECOND local Hom. -/
def target :=
  (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars (RingEquiv.opOp R).toRingHom)).obj
    (NoncommLocalHom.obj (NoncommLocalHom.opScalarHom h hc)
      (NoncommLocalHom.opScalarHom_central h hc) Y B J)

/-- Curry actual local evaluation: restrict m to each chart, apply e to b,
and evaluate that local transformation. No tensor/Hom isomorphism is assumed. -/
def sectionMap (U : Y.Etaleᵒᵖ) (m : F.obj.obj U) :
    (target h hc Y B J).obj.obj U :=
  { app := fun V ↦
      -- Local instance justification (defeq pin): the source of this local map is B restricted along the specified opposite scalar hom.
      letI := Module.compHom (B.obj.obj (op V.unop.left)) (NoncommLocalHom.opScalarHom h hc)
      ConcreteCategory.ofHom (C := ModuleCat.{u + 1} A) (show
        (NoncommLocalHom.modules (NoncommLocalHom.opScalarHom h hc)).obj
          (B.obj.obj (op V.unop.left)) →ₗ[A] J.obj.obj (op V.unop.left) from
      { toFun := fun b ↦ NoncommLocalHomEvaluation.evaluation h hc Y F J (op V.unop.left)
          (((e.hom.app (op V.unop.left)).hom) b)
          ((F.obj.map V.unop.hom.op).hom m)
        map_add' := by sorry
        map_smul' := by sorry })
    naturality := by sorry }

/-- Transpose a specified right-R-linear sheaf pairing to an actual left-R
sheaf map, using the same central A and canonical double-opposite normalization. -/
def map : F ⟶ target h hc Y B J :=
  ObjectProperty.homMk
    { app := fun U ↦
        -- Local instance justification (defeq pin): target uses precisely this double-opposite scalar restriction.
        letI := Module.compHom
          ((NoncommLocalHom.obj (NoncommLocalHom.opScalarHom h hc)
            (NoncommLocalHom.opScalarHom_central h hc) Y B J).obj.obj U)
          (RingEquiv.opOp R).toRingHom
        ConcreteCategory.ofHom (C := ModuleCat.{u + 1} R) (show F.obj.obj U →ₗ[R] (target h hc Y B J).obj.obj U from
        { toFun := sectionMap h hc Y F B J e U
          map_add' := by sorry
          map_smul' := by sorry })
      naturality := by sorry }

end LocalHomTranspose
