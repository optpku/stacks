/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationRestriction

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

namespace EtaleRestriction

variable {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
  (V : smallEtaleSite X)

/-- A nonempty left-Kan index supplies an actual lift of the target chart to `U`. -/
def liftChart (q : CostructuredArrow (etaleRestriction f).op (Opposite.op V)) :
    smallEtaleSite U :=
  smallEtaleSite.mk (ofOverMap q.hom.unop.left ≫ q.left.unop.hom) sorry

/-- The lifted chart, with its identity scheme map, is a left-Kan index object. -/
def terminalChart (q : CostructuredArrow (etaleRestriction f).op (Opposite.op V)) :
    CostructuredArrow (etaleRestriction f).op (Opposite.op V) :=
  CostructuredArrow.mk (Y := Opposite.op (liftChart f V q))
    (MorphismProperty.CostructuredArrow.homMk
      (A := V) (B := (etaleRestriction f).obj (liftChart f V q))
      (𝟙 V.left) trivial sorry).op

/-- Monicity makes every chart lift agree with the lift supplied by `q`. -/
theorem liftChart_w [Mono f]
    (q r : CostructuredArrow (etaleRestriction f).op (Opposite.op V)) :
    ofOverMap r.hom.unop.left ≫ r.left.unop.hom = (liftChart f V q).hom := sorry

/-- The actual map into the terminal left-Kan index uses the original scheme arrow. -/
def toTerminalChart [Mono f]
    (q r : CostructuredArrow (etaleRestriction f).op (Opposite.op V)) :
    r ⟶ terminalChart f V q :=
  CostructuredArrow.homMk
    (MorphismProperty.CostructuredArrow.homMk
      (A := liftChart f V q) (B := r.left.unop)
      r.hom.unop.left trivial (liftChart_w f V q r)).op sorry

/-- The comma triangle determines the underlying scheme map into the terminal lift. -/
theorem toTerminalChart_unique [Mono f]
    (q r : CostructuredArrow (etaleRestriction f).op (Opposite.op V))
    (m : r ⟶ terminalChart f V q) : m = toTerminalChart f V q r := sorry

/-- The specified lift is terminal, with explicit incoming morphisms. -/
def terminalChartIsTerminal [Mono f]
    (q : CostructuredArrow (etaleRestriction f).op (Opposite.op V)) :
    IsTerminal (terminalChart f V q) :=
  IsTerminal.ofUniqueHom (toTerminalChart f V q) (toTerminalChart_unique f V q)

end EtaleRestriction

/-- For a monomorphism, each left-Kan index is empty or has the specified terminal chart.
Only an initial coefficient object is needed in the empty case. -/
instance etaleRestriction_op_hasPointwiseLeftKanExtension_of_mono
    {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] [Mono f]
    {A : Type v} [Category.{w} A] [HasInitial A]
    (F : (smallEtaleSite U)ᵒᵖ ⥤ A) :
    (etaleRestriction f).op.HasPointwiseLeftKanExtension F := by
  classical
  intro V
  let J := CostructuredArrow (etaleRestriction f).op V
  let D := CostructuredArrow.proj (etaleRestriction f).op V ⋙ F
  by_cases h : Nonempty J
  · let q := h.some
    exact HasColimit.mk
      { cocone := coconeOfDiagramTerminal
          (EtaleRestriction.terminalChartIsTerminal f V.unop q) D
        isColimit := colimitOfDiagramTerminal
          (EtaleRestriction.terminalChartIsTerminal f V.unop q) D }
  · let c : Cocone D :=
      { pt := ⊥_ A
        ι := { app := fun q ↦ (h ⟨q⟩).elim, naturality := fun q _ _ ↦ (h ⟨q⟩).elim } }
    exact HasColimit.mk
      { cocone := c
        isColimit :=
          { desc := fun c' ↦ initial.to c'.pt
            fac := fun _ q ↦ (h ⟨q⟩).elim
            uniq := fun c' m _ ↦ initial.hom_ext m (initial.to c'.pt) } }

/-- Abelian sheaves on the small étale site of an algebraic space admit sheafification
in the coefficient universe of the site's morphisms. -/
instance smallEtaleTopology_hasSheafify_addCommGrpCat (X : AlgebraicSpace S) :
    HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1} := by
  infer_instance

/-- Commutative-ring-valued sheaves on the small étale site of an algebraic space
admit weak sheafification. -/
instance smallEtaleTopology_hasWeakSheafify_commRingCat (X : AlgebraicSpace S) :
    HasWeakSheafify (smallEtaleTopology X) CommRingCat.{u + 1} := by
  infer_instance

/-- Ring-valued sheaves on the small étale site of an algebraic space admit weak
sheafification. -/
instance smallEtaleTopology_hasWeakSheafify_ringCat (X : AlgebraicSpace S) :
    HasWeakSheafify (smallEtaleTopology X) RingCat.{u + 1} := by
  infer_instance

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

/-- The canonical adjunction `f_! ⊣ f⁻¹` for étale extension by zero and restriction. -/
def etaleExtensionByZero_adjunction {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] (A : Type v) [Category.{w} A]
    [∀ F : (smallEtaleSite U)ᵒᵖ ⥤ A, (etaleRestriction f).op.HasLeftKanExtension F]
    [HasWeakSheafify (smallEtaleTopology X) A] :
    etaleExtensionByZero f A ⊣ etaleRestrictionSheaf f A :=
  Functor.sheafAdjunctionContinuous (etaleRestriction f) A
    (smallEtaleTopology U) (smallEtaleTopology X)

/-- Extension by zero for sheaves of abelian groups on small étale sites of algebraic
spaces. -/
noncomputable abbrev abelianExtensionByZero {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  etaleExtensionByZero f AddCommGrpCat.{u + 1}

/-- The extension-by-zero/restriction adjunction for abelian sheaves. -/
def abelianExtensionByZero_adjunction {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    abelianExtensionByZero f ⊣ etaleRestrictionSheaf f AddCommGrpCat.{u + 1} :=
  etaleExtensionByZero_adjunction f AddCommGrpCat.{u + 1}

/-- The comparison morphism `ℤ̲_U ⟶ f⁻¹ ℤ̲_X` obtained by sheafifying the
identification of constant presheaves along étale restriction. -/
noncomputable def constantIntegerPullbackHom {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology U) ⟶
      (etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).obj (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X)) :=
  let M := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let adjU := sheafificationAdjunction (smallEtaleTopology U) AddCommGrpCat.{u + 1}
  let adjX := sheafificationAdjunction (smallEtaleTopology X) AddCommGrpCat.{u + 1}
  (adjU.homEquiv ((Functor.const _).obj M)
      ((etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).obj
        (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X)))).symm
    ((Functor.constCompWhiskeringLeftIso ((smallEtaleSite U)ᵒᵖ)
          (C := AddCommGrpCat.{u + 1}) (etaleRestriction f).op).inv.app M ≫
      Functor.whiskerLeft (etaleRestriction f).op (adjX.unit.app ((Functor.const _).obj M)))

/-- The opposite restriction functor has genuine pointwise Kan extensions in
the coefficient universe of the small chart categories. -/
instance etaleRestriction_op_hasPointwiseRightKanExtension_addCommGrpCat
    {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    (P : (smallEtaleSite U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (etaleRestriction f).op.HasPointwiseRightKanExtension P :=
  fun _ ↦ inferInstance

/-- The canonical constant-integer comparison and the restriction comparison are
mutually inverse morphisms of abelian sheaves. -/
theorem constantIntegerPullbackIso_laws {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    let e := ((etaleRestriction f).constantSheafRestrictionIso
      (smallEtaleTopology U) (smallEtaleTopology X) AddCommGrpCat.{u + 1}).app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    (constantIntegerPullbackHom f ≫ e.hom =
      𝟙 (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology U))) ∧
    (e.hom ≫ constantIntegerPullbackHom f =
      𝟙 ((etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).obj
        (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X)))) :=
  sorry

/-- Restriction of the constant integer sheaf has both maps from the actual
restriction/Ran and constant/global-sections adjunctions. The forward leg is
the original sheafification adjunct of the constant presheaf comparison. -/
noncomputable def constantIntegerPullbackIso {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology U) ≅
      (etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).obj (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X)) :=
  let e := ((etaleRestriction f).constantSheafRestrictionIso
    (smallEtaleTopology U) (smallEtaleTopology X) AddCommGrpCat.{u + 1}).app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  { hom := constantIntegerPullbackHom f
    inv := e.hom
    hom_inv_id := (constantIntegerPullbackIso_laws f).1
    inv_hom_id := (constantIntegerPullbackIso_laws f).2 }

/-- The forward constant comparison is the original specified section map. -/
@[simp]
theorem constantIntegerPullbackIso_hom {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] :
    (constantIntegerPullbackIso f).hom = constantIntegerPullbackHom f := rfl

/-- The specified constant comparison is invertible by its constructed inverse. -/
instance isIso_constantIntegerPullbackHom {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] : IsIso (constantIntegerPullbackHom f) :=
  (constantIntegerPullbackIso f).isIso_hom

/-- The trace morphism `Tr_f : f_! ℤ̲_U ⟶ ℤ̲_X`, adjunct of the canonical
identification `ℤ̲_U ⟶ f⁻¹ ℤ̲_X`. -/
noncomputable def traceMap {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] :
    (abelianExtensionByZero f).obj (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology U)) ⟶ CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X) :=
  ((abelianExtensionByZero_adjunction f).homEquiv
      (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology U)) (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X))).symm
    (constantIntegerPullbackHom f)

/-- The trace is the adjunct of the forward comparison `ℤ̲_U ⟶ f⁻¹ ℤ̲_X`. -/
theorem traceMap_spec {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] :
    (abelianExtensionByZero_adjunction f).homEquiv
        (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology U)) (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X)) (traceMap f) =
      constantIntegerPullbackHom f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
