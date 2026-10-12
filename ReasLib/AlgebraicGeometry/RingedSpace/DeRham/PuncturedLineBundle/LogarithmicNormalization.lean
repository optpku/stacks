/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.Geometry
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DeRham.Wedge
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections

@[expose] public section

open CategoryTheory ComplexShape Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle

variable {S X : Scheme.{u}} (f : X ⟶ S) (ℒ : X.Modules)
variable [Scheme.Modules.Invertible ℒ]
variable (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
variable [Scheme.IsRelativeSpectrumOver P]

/-- Left wedge by the logarithmic differential of a punctured-space unit, applied to a
pulled-back relative form. The differential is concretely the basic form `v⁻¹ dv`. -/
noncomputable def logarithmicWedgeSection (n : ℕ) (U : X.Opens)
    (v : ((puncturedOpen ℒ P).toScheme.presheaf.obj
      (op (puncturedProjection ℒ P ⁻¹ᵁ U)))ˣ)
    (ω : (RingedSpace.DeRham.term f.toLRSHom.toShHom n).val.obj (op U)) :
    (RingedSpace.DeRham.term (puncturedProjection ℒ P ≫ f).toLRSHom.toShHom (1 + n)).val.obj
      (op (puncturedProjection ℒ P ⁻¹ᵁ U)) :=
  let g := (puncturedProjection ℒ P ≫ f).toLRSHom.toShHom
  let V := op (puncturedProjection ℒ P ⁻¹ᵁ U)
  let dlogv := SheafOfModules.RingedSite.DeRham.basic
    (RingedSpace.DeRham.structureMap g) 1 V (v⁻¹).val (fun _ ↦ v.val)
  let pullω := ((RingedSpace.DeRham.map (deRhamSquare f ℒ P)).f n).val.app (op U) ω
  ((SheafOfModules.RingedSite.DeRham.wedgeComponent
    (RingedSpace.DeRham.structureMap g) 1 n).val.app V)
      (SheafOfModules.RingedSite.tensorSection
        (RingedSpace.DeRham.coefficients g) V dlogv pullω)

/-- A weight-zero presentation has the geometric normalization when its local splitting,
after the homogeneous inclusion, is left wedge by the actual tautological logarithmic
differential on every section germ. -/
def IsGeometric (D : WeightZeroDeRham f ℒ P) : Prop :=
  ∀ (n : ℕ) (U : X.Opens) (x : X) (hx : x ∈ U)
    (s : ℒ.val.obj (op U))
    (hs : IsStalkGenerator ℒ x (TopCat.Presheaf.germ ℒ.val.presheaf U x hx s))
    (v : ((puncturedOpen ℒ P).toScheme.presheaf.obj
      (op (puncturedProjection ℒ P ⁻¹ᵁ U)))ˣ),
    v.val = puncturedTautological ℒ P U s →
    ∀ (ω : (RingedSpace.DeRham.term f.toLRSHom.toShHom n).val.obj (op U)),
      let q : ℤ := n
      let p : ℤ := (1 + n : ℕ)
      let e := (RingedSpace.DeRham.complex f.toLRSHom.toShHom).extendXIso
        embeddingUpNat (show embeddingUpNat.f n = q from rfl)
      let eP := ((RingedSpace.DeRham.pushforwardComplex (deRhamSquare f ℒ P)).obj
        (RingedSpace.DeRham.complex (puncturedProjection ℒ P ≫ f).toLRSHom.toShHom)).extendXIso
          embeddingUpNat (show embeddingUpNat.f (1 + n) = p from rfl)
      ((stalkFunctor f x).map (D.zeroInclusion.f p)).hom
        ((D.dlogWedge q p (by dsimp [q, p]; omega) x
          (TopCat.Presheaf.germ ℒ.val.presheaf U x hx s) hs).hom
            (TopCat.Presheaf.germ ((ordinaryComplex f).X q).val.presheaf U x hx
              (e.inv.val.app (op U) ω))) =
        TopCat.Presheaf.germ ((pushedForwardDeRham f ℒ P).X p).val.presheaf U x hx
          (eP.inv.val.app (op U) (logarithmicWedgeSection f ℒ P n U v ω))

end AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle
