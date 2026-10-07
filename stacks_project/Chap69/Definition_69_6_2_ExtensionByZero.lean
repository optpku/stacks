module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import stacks_project.Chap66.Lemma_66_18_12_Restriction

/-!
# Extension by zero along étale morphisms of algebraic spaces

An étale morphism `f : U ⟶ X` of algebraic spaces induces extension by zero
`f_!` as the sheaf pullback of étale restriction, left adjoint to `f⁻¹`. The
trace `Tr_f : f_! ℤ̲ ⟶ ℤ̲` is the adjunct of the canonical identification
`ℤ̲_U ≅ f⁻¹ ℤ̲_X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Left Kan extensions along the opposite of étale restriction exist on the small
étale sites of algebraic spaces. -/
instance etaleRestriction_op_hasLeftKanExtension
    {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    {A : Type v} [Category.{w} A] (F : (smallEtaleSite U)ᵒᵖ ⥤ A) :
    (etaleRestriction f).op.HasLeftKanExtension F :=
  sorry

/-- Abelian sheaves on the small étale site of an algebraic space admit sheafification
in the coefficient universe of the site's morphisms. -/
instance smallEtaleTopology_hasSheafify_addCommGrpCat (X : AlgebraicSpace S) :
    HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  sorry

/-- Commutative-ring-valued sheaves on the small étale site of an algebraic space
admit weak sheafification. -/
instance smallEtaleTopology_hasWeakSheafify_commRingCat (X : AlgebraicSpace S) :
    HasWeakSheafify (smallEtaleTopology X) CommRingCat.{u + 1} :=
  sorry

/-- Ring-valued sheaves on the small étale site of an algebraic space admit weak
sheafification. -/
instance smallEtaleTopology_hasWeakSheafify_ringCat (X : AlgebraicSpace S) :
    HasWeakSheafify (smallEtaleTopology X) RingCat.{u + 1} :=
  sorry

/-- Coefficient change from commutative rings to rings preserves sheaves on the small
étale topology of an algebraic space. -/
instance smallEtaleTopology_hasSheafCompose_commRingCat (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  sorry

/-- Coefficient change from rings to abelian groups preserves sheaves on the small
étale topology of an algebraic space. -/
instance smallEtaleTopology_hasSheafCompose_ringCat (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
  sorry

/-- On the small étale topology of an algebraic space, sheafification equivalences of
abelian sheaves in the morphism universe are the locally bijective morphisms. -/
instance smallEtaleTopology_wEqualsLocallyBijective_addCommGrpCat
    (X : AlgebraicSpace S) :
    (smallEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  sorry

/-- Under the canonical Kan-extension and sheafification hypotheses, étale sheaf
restriction on algebraic spaces is a right adjoint. -/
instance etaleRestrictionSheaf_isRightAdjoint {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] (A : Type v) [Category.{w} A]
    [∀ F : (smallEtaleSite U)ᵒᵖ ⥤ A, (etaleRestriction f).op.HasLeftKanExtension F]
    [HasWeakSheafify (smallEtaleTopology X) A] :
    (etaleRestrictionSheaf f A).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (etaleRestriction f) A (smallEtaleTopology U) (smallEtaleTopology X)).isRightAdjoint

/-- The canonical sheaf-valued extension-by-zero functor along an étale morphism of
algebraic spaces, given by the sheaf pullback of étale restriction. -/
noncomputable abbrev etaleExtensionByZero {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] (A : Type v) [Category.{w} A]
    [∀ F : (smallEtaleSite U)ᵒᵖ ⥤ A, (etaleRestriction f).op.HasLeftKanExtension F]
    [HasWeakSheafify (smallEtaleTopology X) A] :
    Sheaf (smallEtaleTopology U) A ⥤ Sheaf (smallEtaleTopology X) A :=
  Functor.sheafPullback (etaleRestriction f) A
    (smallEtaleTopology U) (smallEtaleTopology X)

/-- Étale extension by zero is the canonical sheaf pullback of étale restriction. -/
theorem etaleExtensionByZero_def {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] (A : Type v) [Category.{w} A]
    [∀ F : (smallEtaleSite U)ᵒᵖ ⥤ A, (etaleRestriction f).op.HasLeftKanExtension F]
    [HasWeakSheafify (smallEtaleTopology X) A] :
    etaleExtensionByZero f A =
      Functor.sheafPullback (etaleRestriction f) A
        (smallEtaleTopology U) (smallEtaleTopology X) :=
  sorry

/-- The canonical adjunction `f_! ⊣ f⁻¹` for étale extension by zero and restriction. -/
def etaleExtensionByZero_adjunction {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] (A : Type v) [Category.{w} A]
    [∀ F : (smallEtaleSite U)ᵒᵖ ⥤ A, (etaleRestriction f).op.HasLeftKanExtension F]
    [HasWeakSheafify (smallEtaleTopology X) A] :
    etaleExtensionByZero f A ⊣ etaleRestrictionSheaf f A :=
  Functor.sheafAdjunctionContinuous (etaleRestriction f) A
    (smallEtaleTopology U) (smallEtaleTopology X)

/-- Étale extension by zero is left adjoint to étale restriction via the
continuous sheaf adjunction. -/
theorem etaleExtensionByZero_adjunction_def {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] (A : Type v) [Category.{w} A]
    [∀ F : (smallEtaleSite U)ᵒᵖ ⥤ A, (etaleRestriction f).op.HasLeftKanExtension F]
    [HasWeakSheafify (smallEtaleTopology X) A] :
    etaleExtensionByZero_adjunction f A =
      Functor.sheafAdjunctionContinuous (etaleRestriction f) A
        (smallEtaleTopology U) (smallEtaleTopology X) :=
  sorry

/-- Extension by zero for sheaves of abelian groups on small étale sites of algebraic
spaces. -/
noncomputable abbrev abelianExtensionByZero {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  etaleExtensionByZero f AddCommGrpCat.{u + 1}

/-- Abelian extension by zero is the generic étale extension functor on abelian
sheaves. -/
theorem abelianExtensionByZero_def {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    abelianExtensionByZero f = etaleExtensionByZero f AddCommGrpCat.{u + 1} :=
  sorry

/-- The extension-by-zero/restriction adjunction for abelian sheaves. -/
def abelianExtensionByZero_adjunction {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    abelianExtensionByZero f ⊣ etaleRestrictionSheaf f AddCommGrpCat.{u + 1} :=
  etaleExtensionByZero_adjunction f AddCommGrpCat.{u + 1}

/-- Abelian extension by zero is the coefficient specialization of the generic
étale adjunction. -/
theorem abelianExtensionByZero_adjunction_def {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    abelianExtensionByZero_adjunction f =
      etaleExtensionByZero_adjunction f AddCommGrpCat.{u + 1} :=
  sorry

/-- The constant sheaf of integers on the small étale site of an algebraic space. -/
abbrev constantIntegerSheaf (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  (constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- The constant integer sheaf is the constant sheaf with value `ULift ℤ`. -/
theorem constantIntegerSheaf_def (X : AlgebraicSpace S) :
    constantIntegerSheaf X =
      (constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  sorry

/-- The comparison morphism `ℤ̲_U ⟶ f⁻¹ ℤ̲_X` obtained by sheafifying the
identification of constant presheaves along étale restriction. -/
noncomputable def constantIntegerPullbackHom {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    constantIntegerSheaf U ⟶
      (etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).obj (constantIntegerSheaf X) :=
  let M := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let adjU := sheafificationAdjunction (smallEtaleTopology U) AddCommGrpCat.{u + 1}
  let adjX := sheafificationAdjunction (smallEtaleTopology X) AddCommGrpCat.{u + 1}
  (adjU.homEquiv ((Functor.const _).obj M)
      ((etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).obj
        (constantIntegerSheaf X))).symm
    ((Functor.constCompWhiskeringLeftIso ((smallEtaleSite U)ᵒᵖ)
          (C := AddCommGrpCat.{u + 1}) (etaleRestriction f).op).inv.app M ≫
      Functor.whiskerLeft (etaleRestriction f).op (adjX.unit.app ((Functor.const _).obj M)))

/-- The comparison `ℤ̲_U ⟶ f⁻¹ ℤ̲_X` is an isomorphism. -/
instance isIso_constantIntegerPullbackHom {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    IsIso (constantIntegerPullbackHom f) :=
  sorry

/-- The constant integer comparison is an isomorphism of sheaves. -/
theorem constantIntegerPullbackHom_spec {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    IsIso (constantIntegerPullbackHom f) :=
  sorry

/-- The trace morphism `Tr_f : f_! ℤ̲_U ⟶ ℤ̲_X`, adjunct of the canonical
identification `ℤ̲_U ⟶ f⁻¹ ℤ̲_X`. -/
noncomputable def traceMap {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] :
    (abelianExtensionByZero f).obj (constantIntegerSheaf U) ⟶ constantIntegerSheaf X :=
  ((abelianExtensionByZero_adjunction f).homEquiv
      (constantIntegerSheaf U) (constantIntegerSheaf X)).symm
    (constantIntegerPullbackHom f)

/-- The trace is the adjunct of the forward comparison `ℤ̲_U ⟶ f⁻¹ ℤ̲_X`. -/
theorem traceMap_spec {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] :
    (abelianExtensionByZero_adjunction f).homEquiv
        (constantIntegerSheaf U) (constantIntegerSheaf X) (traceMap f) =
      constantIntegerPullbackHom f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
