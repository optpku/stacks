/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.TensorPower
public import Mathlib.CategoryTheory.Subobject.FactorThru
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Symmetric.Lift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear

/-!
# Geometric multiplication and restriction of line-bundle forms

The maps below are fixed by the relative-spectrum universal map and the de Rham map
of the punctured-open immersion. They are constructed before any homogeneous pieces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle

variable {S X : Scheme.{u}} (f : X ⟶ S) (ℒ : X.Modules)
variable [Scheme.Modules.Invertible ℒ]
variable (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
variable [hP : Scheme.IsRelativeSpectrumOver P]

/-- The commutative square used to push the relative de Rham complex of the total line bundle
to `X`. -/
theorem totalDeRhamSquare :
    CommSq (Scheme.associatedVectorBundleπ ℒ P).toLRSHom.toShHom
      (Scheme.associatedVectorBundleπ ℒ P ≫ f).toLRSHom.toShHom
      f.toLRSHom.toShHom (𝟙 S : S ⟶ S).toLRSHom.toShHom := sorry

/-- The pushed-forward relative de Rham complex of the total line bundle over `S`. -/
noncomputable def totalPushedForwardDeRham :
    CochainComplex (Modules f.toLRSHom.toShHom) ℤ :=
  ((RingedSpace.DeRham.pushforwardComplex (totalDeRhamSquare f ℒ P)).obj
      (RingedSpace.DeRham.complex
        (Scheme.associatedVectorBundleπ ℒ P ≫ f).toLRSHom.toShHom)).extend embeddingUpNat

/-- The canonical map from ordinary relative forms on `X` to the pushed-forward forms on the
total line bundle. -/
noncomputable def ordinaryToTotalPushedForward :
    (RingedSpace.DeRham.complex f.toLRSHom.toShHom).extend embeddingUpNat ⟶
      totalPushedForwardDeRham f ℒ P :=
  HomologicalComplex.extendMap
    (RingedSpace.DeRham.map (totalDeRhamSquare f ℒ P)) embeddingUpNat

/-- Restriction of scalars from `𝒪_X` to `f⁻¹𝒪_S`, used to compare the geometric
homogeneous `𝒪_X`-modules with the terms of the pushed-forward de Rham complexes. -/
abbrev restrictToBaseModules :
    X.Modules ⥤ Modules f.toLRSHom.toShHom :=
  SheafOfModules.RingedSite.restrictionAlong.{u, u, u, u}
    (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom)

/-- The actual degree-`p` punctured relative form pushed forward to `X` is quasicoherent. -/
theorem puncturedAmbientForm_isQuasicoherent (p : ℕ) :
    ((Scheme.Modules.pushforward (puncturedProjection ℒ P)).obj
      (RingedSpace.DeRham.form
        (puncturedProjection ℒ P ≫ f).toLRSHom.toShHom p)).IsQuasicoherent := sorry

/-- The actual degree-`p` punctured relative form pushed forward to `X`. -/
noncomputable def puncturedAmbientForm (p : ℕ) : Scheme.QCoh X :=
  ⟨(Scheme.Modules.pushforward (puncturedProjection ℒ P)).obj
      (RingedSpace.DeRham.form
        (puncturedProjection ℒ P ≫ f).toLRSHom.toShHom p),
    puncturedAmbientForm_isQuasicoherent f ℒ P p⟩

/-- The actual degree-`p` total-line-bundle relative form pushed forward to `X` is
quasicoherent. -/
theorem totalAmbientForm_isQuasicoherent (p : ℕ) :
    ((Scheme.Modules.pushforward (Scheme.associatedVectorBundleπ ℒ P)).obj
      (RingedSpace.DeRham.form
        (Scheme.associatedVectorBundleπ ℒ P ≫ f).toLRSHom.toShHom p)).IsQuasicoherent := sorry

/-- The actual degree-`p` total-line-bundle relative form pushed forward to `X`. -/
noncomputable def totalAmbientForm (p : ℕ) : Scheme.QCoh X :=
  ⟨(Scheme.Modules.pushforward (Scheme.associatedVectorBundleπ ℒ P)).obj
      (RingedSpace.DeRham.form
        (Scheme.associatedVectorBundleπ ℒ P ≫ f).toLRSHom.toShHom p),
    totalAmbientForm_isQuasicoherent f ℒ P p⟩

/-- The fibrewise linear function corresponding to a section of the line bundle. -/
def totalTautological (U : X.Opens) (s : ℒ.val.obj (Opposite.op U)) :
    P.scheme.presheaf.obj (Opposite.op (P.π ⁻¹ᵁ U)) :=
  (P.universalMap.right.hom.app (Opposite.op U)).hom
    (((Scheme.SymmetricAlgebra.ι ℒ).val.app (Opposite.op U)).hom s)

/-- Restriction of the fibrewise linear function to the complement of the zero section. -/
def puncturedTautological (U : X.Opens) (s : ℒ.val.obj (Opposite.op U)) :
    (puncturedOpen ℒ P).toScheme.presheaf.obj
      (Opposite.op (puncturedProjection ℒ P ⁻¹ᵁ U)) :=
  ((puncturedOpen ℒ P).ι.c.app (Opposite.op (P.π ⁻¹ᵁ U))).hom
    (totalTautological ℒ P U s)

/-- Actual scalar multiplication of a relative form by a tautological linear function. -/
def puncturedScalarAction (p : ℕ) (U : X.Opens)
    (a : (puncturedOpen ℒ P).toScheme.presheaf.obj
      (Opposite.op (puncturedProjection ℒ P ⁻¹ᵁ U)))
    (m : (RingedSpace.DeRham.form (puncturedProjection ℒ P ≫ f).toShHom p).val.obj
      (Opposite.op (puncturedProjection ℒ P ⁻¹ᵁ U))) :
    (puncturedAmbientForm f ℒ P p).obj.val.obj (Opposite.op U) := a • m

set_option backward.isDefEq.respectTransparency false in
/-- Restriction-compatible bilinear multiplication by linear functions. -/
def tautologicalBilinear (p : ℕ) :
    SheafOfModules.RingedSite.SectionBilinearMap.{u, u} X.sheaf
      (puncturedAmbientForm f ℒ P p).obj ℒ (puncturedAmbientForm f ℒ P p).obj where
  app U :=
    { toFun := fun m =>
        { toFun := fun s => puncturedScalarAction f ℒ P p U.unop
            (puncturedTautological ℒ P U.unop s) m
          map_add' := by
            intro s t
            simp only [puncturedScalarAction, puncturedTautological, totalTautological,
              map_add, add_smul]
          map_smul' := by sorry }
      map_add' := by
        intro m m'
        ext s
        simp only [LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk,
          puncturedScalarAction, smul_add]
      map_smul' := by sorry }
  naturality := by sorry

/-- Tensor descent of geometric multiplication; its section function is fixed above. -/
theorem tautologicalBilinear_apply (p : ℕ) (U : X.Opens)
    (m : (puncturedAmbientForm f ℒ P p).obj.val.obj (Opposite.op U))
    (s : ℒ.val.obj (Opposite.op U)) :
    (tautologicalBilinear f ℒ P p).app (Opposite.op U) m s =
      puncturedScalarAction f ℒ P p U (puncturedTautological ℒ P U s) m := rfl

/-- Tensor descent of geometric multiplication; its section function is fixed above. -/
def tautologicalMultiplication (p : ℕ) :
    (puncturedAmbientForm f ℒ P p).obj ⊗ ℒ ⟶
      (puncturedAmbientForm f ℒ P p).obj :=
  (tautologicalBilinear f ℒ P p).hom

/-- Geometric multiplication sends a pure tensor to multiplication by its linear function. -/
theorem tautologicalMultiplication_tensorSection (p : ℕ) (U : X.Opens)
    (m : (puncturedAmbientForm f ℒ P p).obj.val.obj (Opposite.op U))
    (s : ℒ.val.obj (Opposite.op U)) :
    (tautologicalMultiplication f ℒ P p).val.app (Opposite.op U)
        (SheafOfModules.RingedSite.tensorSection X.sheaf (Opposite.op U) m s) =
      puncturedScalarAction f ℒ P p U (puncturedTautological ℒ P U s) m :=
  SheafOfModules.RingedSite.SectionBilinearMap.hom_tensorSection.{u, u, u}
    (tautologicalBilinear f ℒ P p) (Opposite.op U) m s

/-- Away from the zero section, the tautological trivialization makes multiplication
invertible on all forms. This is a geometric theorem, not an input comparison assumption. -/
instance tautologicalMultiplication_isIso (p : ℕ) :
    IsIso (tautologicalMultiplication f ℒ P p) := by sorry

/-- The actual square of the punctured-open immersion over the base scheme. -/
theorem restrictionSquare :
    CommSq (puncturedOpen ℒ P).ι.toShHom
      (puncturedProjection ℒ P ≫ f).toShHom (P.π ≫ f).toShHom
      (𝟙 S : S ⟶ S).toShHom := by sorry

/-- Pullback of forms along the open immersion, with the actual de Rham map on sections. -/
def openFormRestriction (p : ℕ) :
    RingedSpace.DeRham.form (P.π ≫ f).toShHom p ⟶
      (Scheme.Modules.pushforward (puncturedOpen ℒ P).ι).obj
        (RingedSpace.DeRham.form (puncturedProjection ℒ P ≫ f).toShHom p) where
  val :=
    { app := fun U => ModuleCat.ofHom (R := P.scheme.presheaf.obj U) (X :=
        (RingedSpace.DeRham.form (P.π ≫ f).toShHom p).val.obj U) (Y :=
        ((Scheme.Modules.pushforward (puncturedOpen ℒ P).ι).obj
          (RingedSpace.DeRham.form (puncturedProjection ℒ P ≫ f).toShHom p)).val.obj U) (show
        (RingedSpace.DeRham.form (P.π ≫ f).toShHom p).val.obj U →ₗ[
          P.scheme.presheaf.obj U]
        ((Scheme.Modules.pushforward (puncturedOpen ℒ P).ι).obj
          (RingedSpace.DeRham.form (puncturedProjection ℒ P ≫ f).toShHom p)).val.obj U from
        { toFun := fun m => ((RingedSpace.DeRham.map (restrictionSquare f ℒ P)).f p).val.app U m
          map_add' := by
            intro m m'
            exact (((RingedSpace.DeRham.map (restrictionSquare f ℒ P)).f p).val.app U).hom.map_add m m'
          map_smul' := by sorry })
      naturality := by sorry }

/-- Restriction from total-space to punctured-space forms, pushed forward to `X`. -/
def restrictionAlongPuncturedOpen (p : ℕ) :
    (totalAmbientForm f ℒ P p).obj ⟶ (puncturedAmbientForm f ℒ P p).obj :=
  (Scheme.Modules.pushforward P.π).map (openFormRestriction f ℒ P p) ≫
    (Scheme.Modules.pushforwardComp (puncturedOpen ℒ P).ι P.π).hom.app _

/-- On sections, open restriction is exactly the degreewise de Rham pullback. -/
theorem restrictionAlongPuncturedOpen_apply (p : ℕ) (U : X.Opens)
    (m : (totalAmbientForm f ℒ P p).obj.val.obj (Opposite.op U)) :
    (restrictionAlongPuncturedOpen f ℒ P p).val.app (Opposite.op U) m =
      ((RingedSpace.DeRham.map (restrictionSquare f ℒ P)).f p).val.app
        (Opposite.op (P.π ⁻¹ᵁ U)) m := rfl

end AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle
