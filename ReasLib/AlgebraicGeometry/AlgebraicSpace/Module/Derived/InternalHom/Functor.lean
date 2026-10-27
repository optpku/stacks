/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InternalHom.Adjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.InternalHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor.Bifunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Functorial derived sheaf Hom and tensor adjunction -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory AlgebraicGeometry ComplexShape

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.privateInPublic true

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The product map induced degreewise by postcomposition in the target complex. -/
private def postDegree (F : CochainComplex X.Modules ℤ)
    {I J : CochainComplex X.Modules ℤ} (g : I ⟶ J) (n : ℤ) :
    (complex F I).X n ⟶ (complex F J).X n :=
  Pi.lift fun i => Pi.π (fun j : ℤ => Modules.InternalHom.obj (F.X j) (I.X (j + n))) i ≫
    Modules.InternalHom.post (F.X i) (g.f (i + n))

/-- Degreewise postcomposition commutes with the Hom differential and is functorial. -/
theorem complexFunctor_laws :
    (∀ (F I : CochainComplex X.Modules ℤ) (n : ℤ), postDegree F (𝟙 I) n = 𝟙 _) ∧
    (∀ (F : CochainComplex X.Modules ℤ) {I J K : CochainComplex X.Modules ℤ}
      (g : I ⟶ J) (h : J ⟶ K) (n : ℤ),
      postDegree F (g ≫ h) n = postDegree F g n ≫ postDegree F h n) ∧
    (∀ (F : CochainComplex X.Modules ℤ) {I J : CochainComplex X.Modules ℤ}
      (g : I ⟶ J) (n m : ℤ),
      postDegree F g n ≫ (complex F J).d n m =
        (complex F I).d n m ≫ postDegree F g m) := sorry

/-- The cochain map induced by postcomposition in the target of sheaf Hom. -/
def complexPost (F : CochainComplex X.Modules ℤ) {I J : CochainComplex X.Modules ℤ}
    (g : I ⟶ J) : complex F I ⟶ complex F J where
  f := postDegree F g
  comm' n m _ := complexFunctor_laws.2.2 F g n m

/-- The product map induced degreewise by precomposition in the source complex. -/
private def preDegree {F' F : CochainComplex X.Modules ℤ} (f : F' ⟶ F)
    (I : CochainComplex X.Modules ℤ) (n : ℤ) :
    (complex F I).X n ⟶ (complex F' I).X n :=
  Pi.lift fun i => Pi.π (fun j : ℤ => Modules.InternalHom.obj (F.X j) (I.X (j + n))) i ≫
    Modules.InternalHom.pre (f.f i) (I.X (i + n))

/-- Degreewise source precomposition commutes with the Hom differential and is contravariant. -/
theorem complexPre_laws :
    (∀ (F I : CochainComplex X.Modules ℤ) (n : ℤ), preDegree (𝟙 F) I n = 𝟙 _) ∧
    (∀ {F'' F' F : CochainComplex X.Modules ℤ} (f : F' ⟶ F) (g : F'' ⟶ F')
      (I : CochainComplex X.Modules ℤ) (n : ℤ),
      preDegree (g ≫ f) I n = preDegree f I n ≫ preDegree g I n) ∧
    (∀ {F' F : CochainComplex X.Modules ℤ} (f : F' ⟶ F)
      (I : CochainComplex X.Modules ℤ) (n m : ℤ),
      preDegree f I n ≫ (complex F' I).d n m =
        (complex F I).d n m ≫ preDegree f I m) := sorry

/-- Source precomposition on the concrete small-universe sheaf Hom complex. -/
def complexPre {F' F : CochainComplex X.Modules ℤ} (f : F' ⟶ F)
    (I : CochainComplex X.Modules ℤ) : complex F I ⟶ complex F' I where
  f := preDegree f I
  comm' n m _ := complexPre_laws.2.2 f I n m

/-- The concrete sheaf Hom complex, covariant in its target. -/
def complexFunctor (F : CochainComplex X.Modules ℤ) :
    CochainComplex X.Modules ℤ ⥤ CochainComplex X.Modules ℤ where
  obj := complex F
  map := complexPost F
  map_id I := HomologicalComplex.Hom.ext (funext (complexFunctor_laws.1 F I))
  map_comp g h := HomologicalComplex.Hom.ext (funext (complexFunctor_laws.2.1 F g h))

/-- Currying on each summand of a total tensor, followed by the Hom product universal map. -/
private def curryDegree {A F I : CochainComplex X.Modules ℤ} (φ : A ⊗ F ⟶ I) (n : ℤ) :
    A.X n ⟶ (complex F I).X n :=
  Pi.lift fun i => Modules.InternalHom.curry
    (HomologicalComplex.ιTensorObj A F n i (i + n) (Int.add_comm n i) ≫ φ.f (i + n))

/-- Evaluation on every tensor summand defines the degreewise uncurrying map. -/
private def uncurryDegree {A F I : CochainComplex X.Modules ℤ} (φ : A ⟶ complex F I)
    (n : ℤ) : (A ⊗ F).X n ⟶ I.X n :=
  HomologicalComplex.mapBifunctorDesc (K₁ := A) (K₂ := F)
    (F := curriedTensor X.Modules) (c := up ℤ) fun a i h =>
      Modules.InternalHom.uncurry
        (φ.f a ≫ Pi.π (fun j : ℤ => Modules.InternalHom.obj (F.X j) (I.X (j + a))) i) ≫
        eqToHom (congrArg I.X ((Int.add_comm i a).trans h))

/-- Both explicit degreewise tensor–Hom transposes commute with the cochain differentials. -/
theorem cochainCurry_laws :
    (∀ {A F I : CochainComplex X.Modules ℤ} (φ : A ⊗ F ⟶ I) (n m : ℤ),
      curryDegree φ n ≫ (complex F I).d n m = A.d n m ≫ curryDegree φ m) ∧
    (∀ {A F I : CochainComplex X.Modules ℤ} (φ : A ⟶ complex F I) (n m : ℤ),
      uncurryDegree φ n ≫ I.d n m = (A ⊗ F).d n m ≫ uncurryDegree φ m) := sorry

/-- Currying a cochain tensor morphism into the actual graded-commutator Hom complex. -/
def cochainCurry {A F I : CochainComplex X.Modules ℤ} (φ : A ⊗ F ⟶ I) :
    A ⟶ complex F I where
  f := curryDegree φ
  comm' n m _ := cochainCurry_laws.1 φ n m

/-- Uncurrying a cochain morphism by explicit evaluation on total-tensor summands. -/
def cochainUncurry {A F I : CochainComplex X.Modules ℤ} (φ : A ⟶ complex F I) :
    A ⊗ F ⟶ I where
  f := uncurryDegree φ
  comm' n m _ := cochainCurry_laws.2 φ n m

/-- The explicit cochain transposes are inverse and natural in both varying arguments. -/
theorem cochainHomEquiv_laws :
    (∀ {A F I : CochainComplex X.Modules ℤ} (φ : A ⊗ F ⟶ I),
      cochainUncurry (cochainCurry φ) = φ) ∧
    (∀ {A F I : CochainComplex X.Modules ℤ} (φ : A ⟶ complex F I),
      cochainCurry (cochainUncurry φ) = φ) ∧
    (∀ {A A' F I : CochainComplex X.Modules ℤ} (a : A' ⟶ A) (φ : A ⟶ complex F I),
      cochainUncurry (a ≫ φ) = (a ⊗ₘ 𝟙 F) ≫ cochainUncurry φ) ∧
    (∀ {A F I J : CochainComplex X.Modules ℤ} (φ : A ⊗ F ⟶ I) (g : I ⟶ J),
      cochainCurry (φ ≫ g) = cochainCurry φ ≫ complexPost F g) := sorry

/-- The concrete cochain tensor–Hom equivalence. -/
def cochainHomEquiv (A F I : CochainComplex X.Modules ℤ) :
    (A ⊗ F ⟶ I) ≃ (A ⟶ complex F I) where
  toFun := cochainCurry
  invFun := cochainUncurry
  left_inv := cochainHomEquiv_laws.1
  right_inv := cochainHomEquiv_laws.2.1

/-- Both cochain transposes preserve the homotopy relation. -/
theorem cochainHomEquiv_homotopy :
    (∀ {A F I : CochainComplex X.Modules ℤ} {φ ψ : A ⊗ F ⟶ I},
      Nonempty (Homotopy φ ψ) → Nonempty (Homotopy (cochainCurry φ) (cochainCurry ψ))) ∧
    (∀ {A F I : CochainComplex X.Modules ℤ} {φ ψ : A ⟶ complex F I},
      Nonempty (Homotopy φ ψ) → Nonempty (Homotopy (cochainUncurry φ) (cochainUncurry ψ))) := sorry

/-- Hom maps induced by precomposition and postcomposition preserve homotopies. -/
theorem complexHomotopy_laws :
    (∀ (F : CochainComplex X.Modules ℤ) {I J : CochainComplex X.Modules ℤ} {g h : I ⟶ J},
      Nonempty (Homotopy g h) → Nonempty (Homotopy (complexPost F g) (complexPost F h))) ∧
    (∀ {F' F : CochainComplex X.Modules ℤ} {f g : F' ⟶ F} (I : CochainComplex X.Modules ℤ),
      Nonempty (Homotopy f g) → Nonempty (Homotopy (complexPre f I) (complexPre g I))) := sorry

/-- Precomposition by a quasi-isomorphism is a quasi-isomorphism of concrete Hom complexes
when the target is K-injective. -/
theorem complexPre_quasiIso {F' F : CochainComplex X.Modules ℤ} (f : F' ⟶ F)
    (I : CochainComplex X.Modules ℤ) (hI : I.IsKInjective) (hf : QuasiIso f) :
    QuasiIso (complexPre f I) := sorry

/-- Internal Hom from the native cell replacement into a K-injective complex is K-injective. -/
theorem cellSource_isKInjective (F I : CochainComplex X.Modules ℤ) (hI : I.IsKInjective) :
    (complex ((Modules.CellTensor.replacement X).obj F) I).IsKInjective := sorry

/-- Localization of the Hom map induced by the specified native cell augmentation. -/
def sourceComparisonIso (F I : CochainComplex X.Modules ℤ) (hI : I.IsKInjective) :
    DerivedCategory.Q.obj (complex F I) ≅
      DerivedCategory.Q.obj (complex ((Modules.CellTensor.replacement X).obj F) I) :=
  Localization.isoOfHom DerivedCategory.Q (HomologicalComplex.quasiIso X.Modules (up ℤ))
    (complexPre ((Modules.CellTensor.augmentation X).app F) I)
    (complexPre_quasiIso _ I hI (SheafOfModules.CellReplacement.augmentation_quasiIso F))

/-- Specified K-injective replacement followed by concrete Hom and localization. -/
def cochain (F : CochainComplex X.Modules ℤ) : CochainComplex X.Modules ℤ ⥤ ModuleDerived X :=
  CochainComplex.KInjectiveResolution.Construction.replacement.{u} X.Modules ⋙
    complexFunctor F ⋙ DerivedCategory.Q

/-- Target-covariant Hom after specified K-injective replacement inverts quasi-isomorphisms. -/
theorem cochain_inverts (F : CochainComplex X.Modules ℤ) :
    (HomologicalComplex.quasiIso X.Modules (up ℤ)).IsInvertedBy (cochain F) := sorry

/-- Derived sheaf Hom from a fixed derived module, formed by formal localization. -/
def functor (E : ModuleDerived X) : ModuleDerived X ⥤ ModuleDerived X :=
  Localization.lift (cochain (DerivedCategory.Q.objPreimage E))
    (cochain_inverts (DerivedCategory.Q.objPreimage E)) DerivedCategory.Q

/-- The derived Hom functor is computed by the specified source representative and target
K-injective replacement. -/
def computationIso (E N : ModuleDerived X) :
    (functor E).obj N ≅ obj E N :=
  ((functor E).mapIso (DerivedCategory.Q.objObjPreimageIso N)).symm ≪≫
    (Localization.fac (cochain (DerivedCategory.Q.objPreimage E))
      (cochain_inverts (DerivedCategory.Q.objPreimage E)) DerivedCategory.Q).app
        (DerivedCategory.Q.objPreimage N)

/-- Source augmentation comparison is natural in K-injective targets and is compatible with
the actual tensor-precomposition and cochain currying square. -/
theorem sourceComparison_laws :
    (∀ (F I J : CochainComplex X.Modules ℤ) (hI : I.IsKInjective) (hJ : J.IsKInjective)
      (g : I ⟶ J),
      DerivedCategory.Q.map (complexPost F g) ≫ (sourceComparisonIso F J hJ).hom =
        (sourceComparisonIso F I hI).hom ≫
          DerivedCategory.Q.map (complexPost ((Modules.CellTensor.replacement X).obj F) g)) ∧
    (∀ {A F I : CochainComplex X.Modules ℤ} (φ : A ⊗ F ⟶ I),
      cochainCurry ((𝟙 A ⊗ₘ (Modules.CellTensor.augmentation X).app F) ≫ φ) =
        cochainCurry φ ≫ complexPre ((Modules.CellTensor.augmentation X).app F) I) := sorry

/-- Tensor–Hom currying descended through the actual homotopy quotient in both directions. -/
private def homotopyHomEquiv (A F I : CochainComplex X.Modules ℤ) :
    ((HomotopyCategory.quotient X.Modules (up ℤ)).obj (A ⊗ F) ⟶
      (HomotopyCategory.quotient X.Modules (up ℤ)).obj I) ≃
    ((HomotopyCategory.quotient X.Modules (up ℤ)).obj A ⟶
      (HomotopyCategory.quotient X.Modules (up ℤ)).obj (complex F I)) where
  toFun := Quot.lift (fun φ => (HomotopyCategory.quotient X.Modules (up ℤ)).map
    (cochainCurry φ)) (fun φ ψ h => CategoryTheory.Quotient.sound _
      (cochainHomEquiv_homotopy.1 ((HomRel.compClosure_iff_self _ φ ψ).mp h)))
  invFun := Quot.lift (fun φ => (HomotopyCategory.quotient X.Modules (up ℤ)).map
    (cochainUncurry φ)) (fun φ ψ h => CategoryTheory.Quotient.sound _
      (cochainHomEquiv_homotopy.2 ((HomRel.compClosure_iff_self _ φ ψ).mp h)))
  left_inv φ := Quot.inductionOn φ fun ψ =>
    congrArg (HomotopyCategory.quotient X.Modules (up ℤ)).map (cochainHomEquiv_laws.1 ψ)
  right_inv φ := Quot.inductionOn φ fun ψ =>
    congrArg (HomotopyCategory.quotient X.Modules (up ℤ)).map (cochainHomEquiv_laws.2.1 ψ)

/-- Homotopy classes of maps into a specified K-injective complex compute derived morphisms. -/
private def localizedHomEquiv (A I : CochainComplex X.Modules ℤ) (hI : I.IsKInjective) :
    ((HomotopyCategory.quotient X.Modules (up ℤ)).obj A ⟶
      (HomotopyCategory.quotient X.Modules (up ℤ)).obj I) ≃
    (DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj I) :=
  (Equiv.ofBijective DerivedCategory.Qh.map
    (@CochainComplex.IsKInjective.Qh_map_bijective X.Modules _ _ _
      ((HomotopyCategory.quotient X.Modules (up ℤ)).obj A) I hI)).trans
      (Iso.homCongr ((DerivedCategory.quotientCompQhIso X.Modules).app A)
        ((DerivedCategory.quotientCompQhIso X.Modules).app I))

/-- The specified K-injective replacement of a derived object's chosen representative. -/
private abbrev resolution (N : ModuleDerived X) : CochainComplex X.Modules ℤ :=
  (CochainComplex.KInjectiveResolution.Construction.replacement.{u} X.Modules).obj
    (DerivedCategory.Q.objPreimage N)

/-- Localization of the specified K-injective augmentation identifies its target with the
original derived object. -/
private def resolutionIso (N : ModuleDerived X) : DerivedCategory.Q.obj (resolution N) ≅ N :=
  (Localization.isoOfHom DerivedCategory.Q (HomologicalComplex.quasiIso X.Modules (up ℤ))
    ((CochainComplex.KInjectiveResolution.Construction.augmentation.{u} X.Modules).app
      (DerivedCategory.Q.objPreimage N))
    (CochainComplex.KInjectiveResolution.Construction.augmentation_quasiIso.{u}
      X.Modules (DerivedCategory.Q.objPreimage N))).symm ≪≫
    DerivedCategory.Q.objObjPreimageIso N

/-- The two-cell computation of fixed-right derived tensor on specified representatives. -/
private def tensorComputation (M E : ModuleDerived X) :
    (DerivedTensor.Right.functor E).obj M ≅
      DerivedCategory.Q.obj
        ((Modules.CellTensor.replacement X).obj (DerivedCategory.Q.objPreimage M) ⊗
          (Modules.CellTensor.replacement X).obj (DerivedCategory.Q.objPreimage E)) :=
  DerivedTensor.Bifunctor.Right.isoAppOf E (Modules.hasDerivedTensorRightCompatible X E) M ≪≫
    (DerivedTensor.Bifunctor.functor (C := X.Modules)).mapIso
      ((DerivedCategory.Q.objObjPreimageIso M).symm.prod
        (DerivedCategory.Q.objObjPreimageIso E).symm) ≪≫
    Modules.CellTensor.computationIso X (DerivedCategory.Q.objPreimage M)
      (DerivedCategory.Q.objPreimage E)

/-- The actual native cell augmentation identifies the localized cell source with its input. -/
private def cellAugmentationIso (F : CochainComplex X.Modules ℤ) :
    DerivedCategory.Q.obj ((Modules.CellTensor.replacement X).obj F) ≅
      DerivedCategory.Q.obj F :=
  Localization.isoOfHom DerivedCategory.Q (HomologicalComplex.quasiIso X.Modules (up ℤ))
    ((Modules.CellTensor.augmentation X).app F)
    (SheafOfModules.CellReplacement.augmentation_quasiIso F)

/-- Derived tensor–Hom currying computed from native cells, K-injective targets, homotopy
currying, and localization of the specified source augmentation. -/
def homEquiv (E M N : ModuleDerived X) :
    ((DerivedTensor.Right.functor E).obj M ⟶ N) ≃ (M ⟶ (functor E).obj N) :=
  let A := DerivedCategory.Q.objPreimage M
  let F := DerivedCategory.Q.objPreimage E
  let I := resolution N
  let hI := CochainComplex.KInjectiveResolution.Construction.replacement_isKInjective.{u}
    X.Modules (DerivedCategory.Q.objPreimage N)
  let A' := (Modules.CellTensor.replacement X).obj A
  let F' := (Modules.CellTensor.replacement X).obj F
  (Iso.homCongr (tensorComputation M E) (resolutionIso N).symm).trans
    ((localizedHomEquiv (A' ⊗ F') I hI).symm.trans
      ((homotopyHomEquiv A' F' I).trans
        ((localizedHomEquiv A' (complex F' I) (cellSource_isKInjective F I hI)).trans
          ((Iso.homCongr (cellAugmentationIso A) (sourceComparisonIso F I hI).symm).trans
            (Iso.homCongr (DerivedCategory.Q.objObjPreimageIso M)
              (computationIso E N).symm)))))

/-- The cell-computed derived tensor–Hom equivalence is natural in its source and target. -/
theorem homEquiv_laws :
    (∀ (E : ModuleDerived X) {M M' N : ModuleDerived X} (f : M' ⟶ M)
      (g : M ⟶ (functor E).obj N),
      (homEquiv E M' N).symm (f ≫ g) =
        (DerivedTensor.Right.functor E).map f ≫ (homEquiv E M N).symm g) ∧
    (∀ (E : ModuleDerived X) {M N N' : ModuleDerived X}
      (f : (DerivedTensor.Right.functor E).obj M ⟶ N) (g : N ⟶ N'),
      homEquiv E M N' (f ≫ g) = homEquiv E M N f ≫ (functor E).map g) := sorry

/-- Fixed-right derived tensor is left adjoint to canonical derived sheaf Hom. -/
def adjunction (E : ModuleDerived X) : DerivedTensor.Right.functor E ⊣ functor E :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv E
      homEquiv_naturality_left_symm := homEquiv_laws.1 E
      homEquiv_naturality_right := homEquiv_laws.2 E }

/-- Derived sheaf Hom from a perfect complex preserves quasi-coherent cohomology. -/
theorem derivedQCoh_of_isPerfect (E : ModuleDerived X) (K : DerivedQCoh X)
    (hE : ModuleDerived.IsPerfect E) :
    derivedQuasiCoherentModuleProperty X ((functor E).obj K.obj) := sorry

/-- Derived sheaf Hom from a pseudo-coherent complex into a bounded-below complex with
quasi-coherent cohomology has quasi-coherent cohomology. -/
theorem derivedQCoh_of_isPseudoCoherent (E : ModuleDerived X) (K : DerivedQCoh X)
    (hE : IsPseudoCoherent X E)
    (hK : (DerivedCategory.TStructure.t.plus : ObjectProperty (ModuleDerived X)) K.obj) :
    derivedQuasiCoherentModuleProperty X ((functor E).obj K.obj) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom
