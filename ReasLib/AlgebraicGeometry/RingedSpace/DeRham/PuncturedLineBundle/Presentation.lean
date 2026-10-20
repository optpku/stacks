/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.Map
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Complement
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.LineBundle.ZeroSection
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Presentations of the weight-zero de Rham complex of a punctured line bundle

This file defines the punctured total space of a line bundle, its pushed-forward relative
de Rham complex, and explicit local-presentation data for its weight-zero subcomplex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle

variable {S X : Scheme.{u}} (f : X ⟶ S) (ℒ : X.Modules)
variable [hℒ : Scheme.Modules.Invertible ℒ]
variable (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
variable [hP : Scheme.IsRelativeSpectrumOver P]

/-- The open complement of the zero section in the total space of a line bundle. -/
def puncturedOpen : (Scheme.associatedVectorBundle ℒ P).Opens :=
  @closedImmersionComplement (Scheme.associatedVectorBundle ℒ P) X
    (@Scheme.AssociatedVectorBundle.zeroSection X (Over.mk (𝟙 X)) ℒ hℒ P hP)
    (@Scheme.AssociatedVectorBundle.zeroSection_isClosedImmersion X
      (Over.mk (𝟙 X)) ℒ hℒ P hP)

/-- The underlying set of the punctured total space is the complement of the image of the
zero section. -/
theorem puncturedOpen_coe :
    (puncturedOpen ℒ P : Set (Scheme.associatedVectorBundle ℒ P)) =
      (Set.range
        (@Scheme.AssociatedVectorBundle.zeroSection X (Over.mk (𝟙 X)) ℒ hℒ P hP).base)ᶜ :=
  sorry

/-- The projection from the punctured total space to the base of the line bundle. -/
noncomputable def puncturedProjection : (puncturedOpen ℒ P).toScheme ⟶ X :=
  (puncturedOpen ℒ P).ι ≫ Scheme.associatedVectorBundleπ ℒ P

/-- The commutative square used to push the relative de Rham complex of the punctured total
space to the base of the line bundle. -/
theorem deRhamSquare :
    CommSq (puncturedProjection ℒ P).toLRSHom.toShHom
      (puncturedProjection ℒ P ≫ f).toLRSHom.toShHom
      f.toLRSHom.toShHom (𝟙 S : S ⟶ S).toLRSHom.toShHom :=
  sorry

/-- The pushed-forward relative de Rham complex of the punctured total space. -/
noncomputable def pushedForwardDeRham :
    CochainComplex (Modules f.toLRSHom.toShHom) ℤ :=
  ((RingedSpace.DeRham.pushforwardComplex (deRhamSquare f ℒ P)).obj
      (RingedSpace.DeRham.complex
        (puncturedProjection ℒ P ≫ f).toLRSHom.toShHom)).extend embeddingUpNat

/-- The canonical map from ordinary relative forms to pushed-forward forms on the punctured
total space. -/
noncomputable def ordinaryToPushedForward :
    (RingedSpace.DeRham.complex f.toLRSHom.toShHom).extend embeddingUpNat ⟶
      pushedForwardDeRham f ℒ P :=
  HomologicalComplex.extendMap
    (RingedSpace.DeRham.map (deRhamSquare f ℒ P)) embeddingUpNat

/-- The ordinary relative de Rham complex, extended from nonnegative to integral degrees. -/
noncomputable abbrev ordinaryComplex :
    CochainComplex (Modules f.toLRSHom.toShHom) ℤ :=
  (RingedSpace.DeRham.complex f.toLRSHom.toShHom).extend embeddingUpNat

/-- The stalk functor for modules over the coefficient sheaf of the relative de Rham
complex. -/
noncomputable def stalkFunctor (x : X) :=
  SheafOfModules.stalkFunctorOfCommRing
    (RingedSpace.DeRham.coefficients f.toLRSHom.toShHom) x

/-- A section of the stalk of `ℒ` at `x` is a generator when its span is the whole stalk. -/
def IsStalkGenerator (x : X) (s : RingedSpace.stalkModuleCat ℒ x) : Prop :=
  Submodule.span (X.presheaf.stalk x) {s} = ⊤

/-- Evaluation of the shifted ordinary de Rham complex in degree `p` is canonically
evaluation of the ordinary complex in degree `q` when `q = p - 1`. -/
noncomputable def shiftedFormIso (q p : ℤ) (h_qp : q = p + (-1 : ℤ)) (x : X) :
    (stalkFunctor f x).obj ((ordinaryComplex f)⟦(-1 : ℤ)⟧.X p) ≅
      (stalkFunctor f x).obj ((ordinaryComplex f).X q) :=
  (stalkFunctor f x).mapIso
    ((ordinaryComplex f).shiftFunctorObjXIso (-1 : ℤ) p q h_qp)

/-- An explicit geometric realization of the weight-zero de Rham complex of a punctured
line bundle.

The componentwise monomorphism identifies `complex` with a homogeneous subcomplex of the
actual pushed-forward de Rham complex. For every local generator `s` of `ℒ`, `dlogWedge`
gives the direct-sum description `ω' + dlog(s) ∧ ω`; changes of generator alter this term by
an ordinary form, and `residue` sends `dlog(s) ∧ ω` to `ω`. -/
structure WeightZeroDeRham.{v}
    {S X : Scheme.{v}} (f : X ⟶ S) (ℒ : X.Modules)
    [hℒ : Scheme.Modules.Invertible ℒ]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
    [hP : Scheme.IsRelativeSpectrumOver P] where
  /-- The degree-zero homogeneous pushed-forward relative de Rham complex. -/
  complex : CochainComplex (Modules f.toLRSHom.toShHom) ℤ
  /-- Inclusion of the degree-zero homogeneous complex into the pushed-forward forms. -/
  zeroInclusion : complex ⟶ pushedForwardDeRham f ℒ P
  /-- Each component is the inclusion of a homogeneous subobject. -/
  zeroInclusion_mono : ∀ p : ℤ, Mono (zeroInclusion.f p)
  /-- The canonical map from ordinary forms to the weight-zero summand. -/
  ordinaryInclusion : ordinaryComplex f ⟶ complex
  /-- The inclusion of ordinary forms agrees with the functorial map to all pushed-forward
  forms. -/
  ordinaryInclusion_zeroInclusion :
    ordinaryInclusion ≫ zeroInclusion = ordinaryToPushedForward f ℒ P
  /-- The residue from weight-zero punctured forms to ordinary forms shifted by `-1`. -/
  residue : complex ⟶ (ordinaryComplex f)⟦(-1 : ℤ)⟧
  /-- Every stalk of `ℒ` admits a generator. -/
  localGenerator_exists :
    ∀ x : X, ∃ s : RingedSpace.stalkModuleCat ℒ x, IsStalkGenerator ℒ x s
  /-- Wedge multiplication by `dlog(s)` sends ordinary degree-`q` forms to degree-`p`
  weight-zero forms when `q = p - 1`. -/
  dlogWedge :
    ∀ (q p : ℤ) (h_qp : q = p + (-1 : ℤ)) (x : X)
      (s : RingedSpace.stalkModuleCat ℒ x) (h_s : IsStalkGenerator ℒ x s),
        (stalkFunctor f x).obj ((ordinaryComplex f).X q) ⟶
          (stalkFunctor f x).obj (complex.X p)
  /-- Every weight-zero form has a unique local decomposition
  `ω' + dlog(s) ∧ ω`. -/
  localDecomposition :
    ∀ (q p : ℤ) (h_qp : q = p + (-1 : ℤ)) (x : X)
      (s : RingedSpace.stalkModuleCat ℒ x) (h_s : IsStalkGenerator ℒ x s),
        IsIso (biprod.desc
          ((stalkFunctor f x).map (ordinaryInclusion.f p))
          (dlogWedge q p h_qp x s h_s))
  /-- Replacing a local generator changes `dlog(s) ∧ -` only by an ordinary form. -/
  changeGenerator :
    ∀ (q p : ℤ) (h_qp : q = p + (-1 : ℤ)) (x : X)
      (s t : RingedSpace.stalkModuleCat ℒ x)
      (h_s : IsStalkGenerator ℒ x s) (h_t : IsStalkGenerator ℒ x t),
        ∃ correction :
            (stalkFunctor f x).obj ((ordinaryComplex f).X q) ⟶
              (stalkFunctor f x).obj ((ordinaryComplex f).X p),
          dlogWedge q p h_qp x s h_s =
            correction ≫ (stalkFunctor f x).map (ordinaryInclusion.f p) +
              dlogWedge q p h_qp x t h_t
  /-- Locally, residue sends `dlog(s) ∧ ω` to `ω` under the shift identification. -/
  residue_dlogWedge :
    ∀ (q p : ℤ) (h_qp : q = p + (-1 : ℤ)) (x : X)
      (s : RingedSpace.stalkModuleCat ℒ x) (h_s : IsStalkGenerator ℒ x s),
        dlogWedge q p h_qp x s h_s ≫
            (stalkFunctor f x).map (residue.f p) =
          (shiftedFormIso f q p h_qp x).inv
  /-- The residue of an ordinary relative form is zero. -/
  inclusion_residue : ordinaryInclusion ≫ residue = 0

namespace WeightZeroDeRham

/-- Build a weight-zero realization from its homogeneous inclusion, local direct-sum
presentations, change-of-generator law, and residue formula. -/
noncomputable def ofLocalPresentation
    (complex : CochainComplex (Modules f.toLRSHom.toShHom) ℤ)
    (zeroInclusion : complex ⟶ pushedForwardDeRham f ℒ P)
    (zeroInclusion_mono : ∀ p : ℤ, Mono (zeroInclusion.f p))
    (ordinaryInclusion : ordinaryComplex f ⟶ complex)
    (ordinaryInclusion_zeroInclusion :
      ordinaryInclusion ≫ zeroInclusion = ordinaryToPushedForward f ℒ P)
    (residue : complex ⟶ (ordinaryComplex f)⟦(-1 : ℤ)⟧)
    (localGenerator_exists :
      ∀ x : X, ∃ s : RingedSpace.stalkModuleCat ℒ x, IsStalkGenerator ℒ x s)
    (dlogWedge :
      ∀ (q p : ℤ) (h_qp : q = p + (-1 : ℤ)) (x : X)
        (s : RingedSpace.stalkModuleCat ℒ x) (h_s : IsStalkGenerator ℒ x s),
          (stalkFunctor f x).obj ((ordinaryComplex f).X q) ⟶
            (stalkFunctor f x).obj (complex.X p))
    (localDecomposition :
      ∀ (q p : ℤ) (h_qp : q = p + (-1 : ℤ)) (x : X)
        (s : RingedSpace.stalkModuleCat ℒ x) (h_s : IsStalkGenerator ℒ x s),
          IsIso (biprod.desc
            ((stalkFunctor f x).map (ordinaryInclusion.f p))
            (dlogWedge q p h_qp x s h_s)))
    (changeGenerator :
      ∀ (q p : ℤ) (h_qp : q = p + (-1 : ℤ)) (x : X)
        (s t : RingedSpace.stalkModuleCat ℒ x)
        (h_s : IsStalkGenerator ℒ x s) (h_t : IsStalkGenerator ℒ x t),
          ∃ correction :
              (stalkFunctor f x).obj ((ordinaryComplex f).X q) ⟶
                (stalkFunctor f x).obj ((ordinaryComplex f).X p),
            dlogWedge q p h_qp x s h_s =
              correction ≫ (stalkFunctor f x).map (ordinaryInclusion.f p) +
                dlogWedge q p h_qp x t h_t)
    (residue_dlogWedge :
      ∀ (q p : ℤ) (h_qp : q = p + (-1 : ℤ)) (x : X)
        (s : RingedSpace.stalkModuleCat ℒ x) (h_s : IsStalkGenerator ℒ x s),
          dlogWedge q p h_qp x s h_s ≫
              (stalkFunctor f x).map (residue.f p) =
            (shiftedFormIso f q p h_qp x).inv)
    (inclusion_residue : ordinaryInclusion ≫ residue = 0) :
    WeightZeroDeRham f ℒ P where
  complex := complex
  zeroInclusion := zeroInclusion
  zeroInclusion_mono := zeroInclusion_mono
  ordinaryInclusion := ordinaryInclusion
  ordinaryInclusion_zeroInclusion := ordinaryInclusion_zeroInclusion
  residue := residue
  localGenerator_exists := localGenerator_exists
  dlogWedge := dlogWedge
  localDecomposition := localDecomposition
  changeGenerator := changeGenerator
  residue_dlogWedge := residue_dlogWedge
  inclusion_residue := inclusion_residue

/-- An explicit weight-zero presentation has componentwise homogeneous inclusion, ordinary
inclusion compatibility, local generators and decompositions, generator-change compatibility,
the local residue formula, and vanishing residue on ordinary forms. -/
theorem spec (D : WeightZeroDeRham f ℒ P) :
    (∀ p : ℤ, Mono (D.zeroInclusion.f p)) ∧
      D.ordinaryInclusion ≫ D.zeroInclusion = ordinaryToPushedForward f ℒ P ∧
      (∀ x : X, ∃ s : RingedSpace.stalkModuleCat ℒ x, IsStalkGenerator ℒ x s) ∧
      (∀ (q p : ℤ) (h_qp : q = p + (-1 : ℤ)) (x : X)
        (s : RingedSpace.stalkModuleCat ℒ x) (h_s : IsStalkGenerator ℒ x s),
          IsIso (biprod.desc
            ((stalkFunctor f x).map (D.ordinaryInclusion.f p))
            (D.dlogWedge q p h_qp x s h_s))) ∧
      (∀ (q p : ℤ) (h_qp : q = p + (-1 : ℤ)) (x : X)
        (s t : RingedSpace.stalkModuleCat ℒ x)
        (h_s : IsStalkGenerator ℒ x s) (h_t : IsStalkGenerator ℒ x t),
          ∃ correction :
              (stalkFunctor f x).obj ((ordinaryComplex f).X q) ⟶
                (stalkFunctor f x).obj ((ordinaryComplex f).X p),
            D.dlogWedge q p h_qp x s h_s =
              correction ≫ (stalkFunctor f x).map (D.ordinaryInclusion.f p) +
                D.dlogWedge q p h_qp x t h_t) ∧
      (∀ (q p : ℤ) (h_qp : q = p + (-1 : ℤ)) (x : X)
        (s : RingedSpace.stalkModuleCat ℒ x) (h_s : IsStalkGenerator ℒ x s),
          D.dlogWedge q p h_qp x s h_s ≫
              (stalkFunctor f x).map (D.residue.f p) =
            (shiftedFormIso f q p h_qp x).inv) ∧
      D.ordinaryInclusion ≫ D.residue = 0 :=
  sorry

end WeightZeroDeRham

end AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle
