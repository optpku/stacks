/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Derivation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Etale.Kaehler

/-!
# Derivations on affine global sections

Taking sections on the top open of an affine scheme sends relative derivations of module sheaves
to derivations of their modules of global sections.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.AffineDerivation

open scoped TensorProduct

open AlgebraicGeometry CategoryTheory Opposite
open scoped AlgebraicGeometry

variable {R A : CommRingCat}

noncomputable def extendDerivation
    (R S T M : Type u) [CommRing R] [CommRing S] [CommRing T]
    [AddCommGroup M] [Algebra R S] [Algebra R T] [Algebra S T]
    [Module R M] [Module S M] [Module T M]
    [IsScalarTower R S T] [IsScalarTower R S M] [IsScalarTower R T M]
    [IsScalarTower S T M] [Algebra.FormallyEtale S T]
    (D : Derivation R S M) : Derivation R T M :=
  ((D.liftKaehlerDifferential.liftBaseChange T).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap).compDer
      (KaehlerDifferential.D R T)

theorem extendDerivation_algebraMap
    (R S T M : Type u) [CommRing R] [CommRing S] [CommRing T]
    [AddCommGroup M] [Algebra R S] [Algebra R T] [Algebra S T]
    [Module R M] [Module S M] [Module T M]
    [IsScalarTower R S T] [IsScalarTower R S M] [IsScalarTower R T M]
    [IsScalarTower S T M] [Algebra.FormallyEtale S T]
    (D : Derivation R S M) (s : S) :
    extendDerivation R S T M D (algebraMap S T s) = D s := by
  simp [extendDerivation, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]

set_option backward.isDefEq.respectTransparency false in
def restrictedDerivation (φ : R ⟶ A) (F : (Spec A).Modules)
    (D : ((moduleSpecΓFunctor (R := A)).obj F).Derivation φ)
    (U : (Spec A).Opens) :
    ((modulesSpecToSheaf.obj F).obj.obj (op U)).Derivation φ :=
  ModuleCat.Derivation.mk
    (fun a => ((modulesSpecToSheaf.obj F).obj.map U.leTop.op).hom (D.d a))
    (by intro a b; rw [D.d_add]; exact ((modulesSpecToSheaf.obj F).obj.map U.leTop.op).hom.map_add _ _)
    (by
      intro a b
      rw [D.d_mul]
      let L := ((modulesSpecToSheaf.obj F).obj.map U.leTop.op).hom
      exact (L.map_add _ _).trans (congrArg₂ (· + ·) (L.map_smul a _) (L.map_smul b _)))
    (by intro a; rw [D.d_map]; exact ((modulesSpecToSheaf.obj F).obj.map U.leTop.op).hom.map_zero)

set_option backward.isDefEq.respectTransparency false in
def basicOpenExtension (φ : R ⟶ A) (F : (Spec A).Modules)
    (D : ((moduleSpecΓFunctor (R := A)).obj F).Derivation φ) (f : A) :
    Γ(Spec A, PrimeSpectrum.basicOpen f) → Γ(F, PrimeSpectrum.basicOpen f) := by
  let U := PrimeSpectrum.basicOpen f
  let T := Γ(Spec A, U)
  let M := Γ(F, U)
  letI := φ.hom.toAlgebra
  letI : Algebra R T := ((algebraMap A T).comp φ.hom).toAlgebra
  letI : Module R M := Module.compHom M φ.hom
  letI : IsScalarTower R A T := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R A M := IsScalarTower.of_compHom R A M
  letI : IsScalarTower R T M := IsScalarTower.of_algebraMap_smul fun r m => by rfl
  letI : Algebra.FormallyEtale A T := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers f)
  exact fun t => (extendDerivation R A T M (restrictedDerivation φ F D U)) t

theorem basicOpenExtension_algebraMap (φ : R ⟶ A) (F : (Spec A).Modules)
    (D : ((moduleSpecΓFunctor (R := A)).obj F).Derivation φ) (f a : A) :
    basicOpenExtension φ F D f (algebraMap A Γ(Spec A, PrimeSpectrum.basicOpen f) a) =
      ((modulesSpecToSheaf.obj F).obj.map (PrimeSpectrum.basicOpen f).leTop.op).hom (D.d a) := by
  dsimp only [basicOpenExtension]
  rw [extendDerivation_algebraMap]
  rfl

variable {R A : CommRingCat.{u}}

/-- Taking sections on the top open of an affine scheme sends a relative sheaf derivation to the
corresponding derivation of the module of global sections. -/
noncomputable def globalSections (φ : R ⟶ A) (ℱ : (Spec A).Modules) :
    SheafOfModules.RelativeDerivation (J := Opens.grothendieckTopology (Spec A))
      (RingedSpace.Hom.inverseImageStructureSheafHomComm (Spec.map φ).toShHom) ℱ →
      ((moduleSpecΓFunctor (R := A)).obj ℱ).Derivation φ :=
  fun D ↦ ModuleCat.Derivation.mk
    (fun a ↦ (D.app (op ⊤)).d ((Scheme.ΓSpecIso A).inv a))
    (by
      intro a b
      simp only [PresheafOfModules.Derivation'.app_apply]
      rw [(Scheme.ΓSpecIso A).inv.hom.map_add]
      exact map_add (D.d (X := op ⊤)) _ _)
    (by
      intro a b
      simp only [PresheafOfModules.Derivation'.app_apply]
      change D.d ((Scheme.ΓSpecIso A).inv (a * b)) =
        (Scheme.ΓSpecIso A).inv a • D.d ((Scheme.ΓSpecIso A).inv b) +
          (Scheme.ΓSpecIso A).inv b • D.d ((Scheme.ΓSpecIso A).inv a)
      rw [(Scheme.ΓSpecIso A).inv.hom.map_mul]
      exact D.d_mul ((Scheme.ΓSpecIso A).inv a) ((Scheme.ΓSpecIso A).inv b))
    (by sorry)

/-- The derivation induced on affine global sections evaluates a sheaf derivation on the top
open after identifying the coefficient ring with the global functions on its spectrum. -/
@[simp]
theorem globalSections_apply (φ : R ⟶ A) (ℱ : (Spec A).Modules)
    (D : SheafOfModules.RelativeDerivation (J := Opens.grothendieckTopology (Spec A))
      (RingedSpace.Hom.inverseImageStructureSheafHomComm (Spec.map φ).toShHom) ℱ)
    (a : A) :
    (globalSections φ ℱ D).d a =
      (D.app (op ⊤)).d ((Scheme.ΓSpecIso A).inv a) := rfl

/-- Taking affine global sections is a bijection from relative derivations of a module sheaf to
relative derivations of its module of global sections. -/
theorem globalSections_bijective (φ : R ⟶ A) (ℱ : (Spec A).Modules) :
    Function.Bijective (globalSections φ ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules.AffineDerivation
