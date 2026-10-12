/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Eta.Functoriality
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower.Graded
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ideal.Eta

/-!
# Affine comparison for eta complexes of ideal sheaves

This file constructs the comparison between the eta complex of affine sections
and the affine sections of the ideal-sheaf eta complex.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.Eta

variable {X : Scheme.{u}}

/-- The complex obtained by taking sections degreewise over the affine open `U`. -/
abbrev affineSectionsComplex (U : X.affineOpens) (K : CochainComplex X.Modules ℤ) :
    CochainComplex (ModuleCat Γ(X, U.1)) ℤ :=
  (RingedSpace.moduleSectionsEvaluationFunctor X.toRingedSpace U.1).mapHomologicalComplex
    (up ℤ) |>.obj K

/-- A generator of an effective Cartier ideal on an affine open acts regularly on
every term of the corresponding sections complex. -/
theorem affineSectionsRegular (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (K : CochainComplex X.Modules ℤ)
    [RingedSpace.IdealSheaf.IsActionMono.Complex D.toSubobject K]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) :
    (affineSectionsComplex U K).IsTermwiseSMulRegular f := sorry

/-- The chosen affine equation belongs to the section ideal of the divisor. -/
theorem affineGenerator_mem_sections (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) :
    f ∈ SheafOfModules.RingedSite.IdealSheaf.sections
      D.toSubobject (Opposite.op U.1) := sorry

/-- The section of the effective-Cartier ideal sheaf represented by the affine equation `f`. -/
noncomputable def affineGeneratorSection (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) :
    D.toSubobject.toModule.val.obj (Opposite.op U.1) :=
  (SheafOfModules.RingedSite.IdealSheaf.sectionsIso
    D.toSubobject (Opposite.op U.1)).inv
      ⟨f, affineGenerator_mem_sections D U f hf⟩

/-- The ideal-sheaf inclusion sends the chosen generator section to `f`. -/
theorem affineGeneratorSection_spec (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) :
    ((D.toSubobject.arrow.val.app (Opposite.op U.1)).hom)
        (affineGeneratorSection D U f hf) = f := sorry

/-- The chosen generator, regarded as a section of the first integral tensor power. -/
noncomputable def affineGeneratorDegreeOne (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) :
    ((D.toSubobject.toModule ^⊗ (1 : ℤ)).val.obj (Opposite.op U.1)) :=
  ((((RingedSpace.InvertiblePower.categoricalIso D.toSubobject.toModule 1) ≪≫
      MonoidalCategory.InvertiblePower.oneIso D.toSubobject.toModule).inv.val.app
        (Opposite.op U.1)).hom) (affineGeneratorSection D U f hf)

/-- Multiplication by the chosen degree-one generator, evaluated against degree `-1`. -/
noncomputable def affineGeneratorEvaluationLinear (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) :
    ((D.toSubobject.toModule ^⊗ (-1 : ℤ)).val.obj (Opposite.op U.1)) →ₗ[Γ(X, U.1)]
      Γ(X, U.1) :=
  ((RingedSpace.InvertiblePower.zeroIso D.toSubobject.toModule).hom.val.app
      (Opposite.op U.1)).hom.comp
    (RingedSpace.InvertiblePower.mulSectionLinear D.toSubobject.toModule
      (Opposite.op U.1) 1 (-1) (affineGeneratorDegreeOne D U f hf))

/-- On a principal effective-Cartier chart, evaluation against the generator identifies the
inverse ideal power with the structure module. -/
theorem affineGeneratorEvaluationLinear_bijective (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) :
    Function.Bijective (affineGeneratorEvaluationLinear D U f hf) := sorry

/-- The degree `-1` section inverse to the chosen affine generator. -/
noncomputable def affineGeneratorInverseSection (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) :
    ((D.toSubobject.toModule ^⊗ (-1 : ℤ)).val.obj (Opposite.op U.1)) :=
  Function.invFun (affineGeneratorEvaluationLinear D U f hf) 1

/-- Evaluating the inverse generator section against the generator gives the unit section. -/
theorem affineGeneratorInverseSection_spec (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) :
    affineGeneratorEvaluationLinear D U f hf
      (affineGeneratorInverseSection D U f hf) = 1 := sorry

/-- The inverse generator section is uniquely characterized by evaluation against the chosen
generator. -/
theorem affineGeneratorInverseSection_unique (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f})
    (s : (D.toSubobject.toModule ^⊗ (-1 : ℤ)).val.obj (Opposite.op U.1))
    (hs : affineGeneratorEvaluationLinear D U f hf s = 1) :
    s = affineGeneratorInverseSection D U f hf := sorry

/-- The nonnegative powers of the chosen affine ideal generator as local tensor-power sections. -/
noncomputable def affineGeneratorNonnegativePowerSection (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) :
    (n : ℕ) → ((D.toSubobject.toModule ^⊗ (n : ℤ)).val.obj (Opposite.op U.1))
  | 0 => RingedSpace.InvertiblePower.oneSection D.toSubobject.toModule (Opposite.op U.1)
  | n + 1 =>
      ((RingedSpace.InvertiblePower.indexIso D.toSubobject.toModule
        ((Int.natCast_add 1 n).symm.trans (congrArg Int.ofNat (Nat.one_add n)))).hom.val.app
          (Opposite.op U.1)).hom
            (RingedSpace.InvertiblePower.mulSection D.toSubobject.toModule
              (Opposite.op U.1) 1 n (affineGeneratorDegreeOne D U f hf)
              (affineGeneratorNonnegativePowerSection D U f hf n))

/-- The negative powers of the chosen affine ideal generator as local tensor-power sections. -/
noncomputable def affineGeneratorNegativePowerSection (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) :
    (n : ℕ) → ((D.toSubobject.toModule ^⊗ Int.negSucc n).val.obj (Opposite.op U.1))
  | 0 => affineGeneratorInverseSection D U f hf
  | n + 1 =>
      ((RingedSpace.InvertiblePower.indexIso D.toSubobject.toModule
        (MonoidalCategory.InvertiblePower.Aux.negSuccEq n).symm).hom.val.app
          (Opposite.op U.1)).hom
            (RingedSpace.InvertiblePower.mulSection D.toSubobject.toModule
              (Opposite.op U.1) (-1) (Int.negSucc n)
              (affineGeneratorInverseSection D U f hf)
              (affineGeneratorNegativePowerSection D U f hf n))

/-- The integral power of the chosen affine generator in the corresponding ideal-sheaf tensor
power. -/
noncomputable def affineGeneratorPowerSection (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) :
    (i : ℤ) → ((D.toSubobject.toModule ^⊗ i).val.obj (Opposite.op U.1))
  | Int.ofNat n => affineGeneratorNonnegativePowerSection D U f hf n
  | Int.negSucc n => affineGeneratorNegativePowerSection D U f hf n

/-- Tensoring a section of `K.X i` with the `i`th power of the affine generator gives the
ambient sheaf-eta section represented by divided-differential coordinates. -/
noncomputable def affineAmbientLinear (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (K : CochainComplex X.Modules ℤ) [∀ i : ℤ, (K.X i).IsQuasicoherent]
    [RingedSpace.IdealSheaf.IsActionMono.Complex D.toSubobject K]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) (i : ℤ) :
    ((CochainComplex.BerthelotOgus.Int.eta f (affineSectionsComplex U K)
      (affineSectionsRegular D K U f hf)).X i) →ₗ[Γ(X, U.1)]
      ((RingedSpace.moduleSectionsEvaluationFunctor X.toRingedSpace U.1).obj
        (RingedSpace.IdealSheaf.Eta.ambient D.toSubobject K i)) :=
  (SheafOfModules.RingedSite.tensorSectionLinear X.toRingedSpace.sheaf
      (D.toSubobject.toModule ^⊗ i) (K.X i) (Opposite.op U.1)
      (affineGeneratorPowerSection D U f hf i)).comp
    (CochainComplex.BerthelotOgus.Int.term f (affineSectionsComplex U K) i).subtype

/-- The ambient affine comparison sends a divided-differential coordinate `x` to the pure tensor
of the chosen generator power with the underlying section of `x`. -/
theorem affineAmbientLinear_apply (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (K : CochainComplex X.Modules ℤ) [∀ i : ℤ, (K.X i).IsQuasicoherent]
    [RingedSpace.IdealSheaf.IsActionMono.Complex D.toSubobject K]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f})
    (i : ℤ) (x : (CochainComplex.BerthelotOgus.Int.eta f
      (affineSectionsComplex U K) (affineSectionsRegular D K U f hf)).X i) :
    affineAmbientLinear D K U f hf i x =
      SheafOfModules.RingedSite.tensorSection X.toRingedSpace.sheaf
        (Opposite.op U.1) (affineGeneratorPowerSection D U f hf i) x.1 := sorry

/-- The explicit ambient map from divided-differential coordinates satisfies the kernel
condition defining the sheaf eta term. -/
theorem affineAmbientLinear_toQuotient (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (K : CochainComplex X.Modules ℤ) [∀ i : ℤ, (K.X i).IsQuasicoherent]
    [RingedSpace.IdealSheaf.IsActionMono.Complex D.toSubobject K]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) (i : ℤ) :
    ModuleCat.ofHom (affineAmbientLinear D K U f hf i) ≫
        (RingedSpace.moduleSectionsEvaluationFunctor X.toRingedSpace U.1).map
          (RingedSpace.IdealSheaf.Eta.toQuotient D.toSubobject K i) = 0 := sorry

/-- The degreewise linear comparison is the canonical lift of tensoring with the chosen
generator power through the kernel defining the sheaf eta term. -/
noncomputable def affineTermLinear (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (K : CochainComplex X.Modules ℤ) [∀ i : ℤ, (K.X i).IsQuasicoherent]
    [RingedSpace.IdealSheaf.IsActionMono.Complex D.toSubobject K]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) (i : ℤ) :
    ((CochainComplex.BerthelotOgus.Int.eta f (affineSectionsComplex U K)
      (affineSectionsRegular D K U f hf)).X i) →ₗ[Γ(X, U.1)]
      ((affineSectionsComplex U
        (RingedSpace.IdealSheaf.Eta.complex D.toSubobject K)).X i) :=
  (CategoryTheory.Limits.kernel.lift
      ((RingedSpace.moduleSectionsEvaluationFunctor X.toRingedSpace U.1).map
        (RingedSpace.IdealSheaf.Eta.toQuotient D.toSubobject K i))
      (ModuleCat.ofHom (affineAmbientLinear D K U f hf i))
      (affineAmbientLinear_toQuotient D K U f hf i) ≫
    (CategoryTheory.Limits.PreservesKernel.iso
      (RingedSpace.moduleSectionsEvaluationFunctor X.toRingedSpace U.1)
      (RingedSpace.IdealSheaf.Eta.toQuotient D.toSubobject K i)).inv).hom

/-- After the eta-kernel inclusion, the affine term comparison is tensoring with the chosen
integral power of the principal generator. -/
theorem affineTermLinear_spec (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (K : CochainComplex X.Modules ℤ) [∀ i : ℤ, (K.X i).IsQuasicoherent]
    [RingedSpace.IdealSheaf.IsActionMono.Complex D.toSubobject K]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) (i : ℤ) :
    ModuleCat.ofHom (affineTermLinear D K U f hf i) ≫
        (RingedSpace.moduleSectionsEvaluationFunctor X.toRingedSpace U.1).map
          (CategoryTheory.Limits.kernel.ι
            (RingedSpace.IdealSheaf.Eta.toQuotient D.toSubobject K i)) =
      ModuleCat.ofHom (affineAmbientLinear D K U f hf i) := sorry

/-- The degreewise affine eta comparison bundled as a morphism of modules. -/
noncomputable def affineTermHom (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (K : CochainComplex X.Modules ℤ) [∀ i : ℤ, (K.X i).IsQuasicoherent]
    [RingedSpace.IdealSheaf.IsActionMono.Complex D.toSubobject K]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) (i : ℤ) :
    (CochainComplex.BerthelotOgus.Int.eta f (affineSectionsComplex U K)
        (affineSectionsRegular D K U f hf)).X i ⟶
      (affineSectionsComplex U
        (RingedSpace.IdealSheaf.Eta.complex D.toSubobject K)).X i :=
  ModuleCat.ofHom (affineTermLinear D K U f hf i)

/-- The underlying linear map of the bundled degreewise comparison. -/
theorem affineTermHom_hom (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (K : CochainComplex X.Modules ℤ) [∀ i : ℤ, (K.X i).IsQuasicoherent]
    [RingedSpace.IdealSheaf.IsActionMono.Complex D.toSubobject K]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) (i : ℤ) :
    (affineTermHom D K U f hf i).hom = affineTermLinear D K U f hf i := sorry

/-- The degreewise affine eta comparison maps commute with the differentials. -/
theorem affineTermHom_comm (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (K : CochainComplex X.Modules ℤ) [∀ i : ℤ, (K.X i).IsQuasicoherent]
    [RingedSpace.IdealSheaf.IsActionMono.Complex D.toSubobject K]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f})
    (i j : ℤ) (_ : (up ℤ).Rel i j) :
    affineTermHom D K U f hf i ≫
        (affineSectionsComplex U
          (RingedSpace.IdealSheaf.Eta.complex D.toSubobject K)).d i j =
      (CochainComplex.BerthelotOgus.Int.eta f (affineSectionsComplex U K)
          (affineSectionsRegular D K U f hf)).d i j ≫
        affineTermHom D K U f hf j := sorry

/-- The canonical cochain morphism from the ring-level affine eta complex to the
sections of the ideal-sheaf eta complex. -/
noncomputable def affineComparison (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (K : CochainComplex X.Modules ℤ) [∀ i : ℤ, (K.X i).IsQuasicoherent]
    [RingedSpace.IdealSheaf.IsActionMono.Complex D.toSubobject K]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) :
    CochainComplex.BerthelotOgus.Int.eta f (affineSectionsComplex U K)
        (affineSectionsRegular D K U f hf) ⟶
      affineSectionsComplex U (RingedSpace.IdealSheaf.Eta.complex D.toSubobject K) where
  f i := affineTermHom D K U f hf i
  comm' i j hij := affineTermHom_comm D K U f hf i j hij

/-- The components of the affine eta comparison are the degreewise comparison maps. -/
theorem affineComparison_f (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (K : CochainComplex X.Modules ℤ) [∀ i : ℤ, (K.X i).IsQuasicoherent]
    [RingedSpace.IdealSheaf.IsActionMono.Complex D.toSubobject K]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) (i : ℤ) :
    (affineComparison D K U f hf).f i = affineTermHom D K U f hf i := sorry

/-- The affine eta comparison is natural for maps of termwise quasicoherent,
ideal-action-monic complexes. -/
theorem affineComparison_naturality (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (K L : CochainComplex X.Modules ℤ)
    [∀ i : ℤ, (K.X i).IsQuasicoherent] [∀ i : ℤ, (L.X i).IsQuasicoherent]
    [RingedSpace.IdealSheaf.IsActionMono.Complex D.toSubobject K]
    [RingedSpace.IdealSheaf.IsActionMono.Complex D.toSubobject L]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f})
    (φ : K ⟶ L) :
    CochainComplex.BerthelotOgus.Int.map f
        ((RingedSpace.moduleSectionsEvaluationFunctor X.toRingedSpace U.1).mapHomologicalComplex
          (up ℤ) |>.map φ)
        (affineSectionsRegular D K U f hf) (affineSectionsRegular D L U f hf) ≫
      affineComparison D L U f hf =
        affineComparison D K U f hf ≫
          ((RingedSpace.moduleSectionsEvaluationFunctor X.toRingedSpace U.1).mapHomologicalComplex
            (up ℤ) |>.map (RingedSpace.IdealSheaf.Eta.map D.toSubobject φ)) := sorry

/-- The canonical affine eta comparison is an isomorphism. -/
instance affineComparisonIsIso (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (K : CochainComplex X.Modules ℤ) [∀ i : ℤ, (K.X i).IsQuasicoherent]
    [RingedSpace.IdealSheaf.IsActionMono.Complex D.toSubobject K]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) :
    IsIso (affineComparison D K U f hf) := sorry

/-- The explicit canonical isomorphism from the ring-level affine eta complex to the
sections of the ideal-sheaf eta complex. -/
noncomputable def affineSectionsIso (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (K : CochainComplex X.Modules ℤ) [∀ i : ℤ, (K.X i).IsQuasicoherent]
    [RingedSpace.IdealSheaf.IsActionMono.Complex D.toSubobject K]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) :
    CochainComplex.BerthelotOgus.Int.eta f (affineSectionsComplex U K)
        (affineSectionsRegular D K U f hf) ≅
      affineSectionsComplex U (RingedSpace.IdealSheaf.Eta.complex D.toSubobject K) :=
  asIso (affineComparison D K U f hf)

/-- The forward morphism of the affine eta isomorphism is the canonical comparison. -/
theorem affineSectionsIso_hom (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (K : CochainComplex X.Modules ℤ) [∀ i : ℤ, (K.X i).IsQuasicoherent]
    [RingedSpace.IdealSheaf.IsActionMono.Complex D.toSubobject K]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}) :
    (affineSectionsIso D K U f hf).hom = affineComparison D K U f hf := sorry

end AlgebraicGeometry.Scheme.IdealSheafData.Eta
