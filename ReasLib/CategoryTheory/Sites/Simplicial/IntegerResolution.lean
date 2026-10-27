/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Adjunction
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import ReasLib.CategoryTheory.Sites.Simplicial.LowerShriek

/-!
# Alternating-face complex of `g_{n!} ℤ` on a morphism diagram of sites

The simplicial abelian sheaf `n ↦ g_{n!} ℤ` on the total site of a morphism
diagram, its augmentation to the constant integer sheaf, and its associated
alternating-face chain complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [∀ n, (ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget AddCommGrpCat.{w})]

/-- The constant sheaf with value `ULift ℤ` on the degree-`n` site. -/
abbrev constantInteger (n : SimplexCategory) :
    Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w} :=
  constantIntegerSheaf (J n).toGrothendieck

/-- Unfolding `constantInteger` recovers `constantIntegerSheaf` on the stage topology. -/
theorem constantInteger_eq (n : SimplexCategory) :
    constantInteger C J n = constantIntegerSheaf (J n).toGrothendieck :=
  rfl

/-- Identification of the pullback of a constant integer presheaf along `u_φ` with
the constant integer sheaf on the source stage. -/
def face_constCompIso {n m : SimplexCategory} (φ : n ⟶ m) :
    (presheafToSheaf ((J n).toGrothendieck) AddCommGrpCat.{w}).obj
      ((C.map φ).toFunctor.op ⋙
        ((Functor.const ((C.obj m)ᵒᵖ)).obj (AddCommGrpCat.of (ULift.{w} ℤ)))) ≅
    constantInteger C J n :=
  (presheafToSheaf ((J n).toGrothendieck) AddCommGrpCat.{w}).mapIso
    ((constCompWhiskeringLeftIso (C.obj n)ᵒᵖ (C.map φ).toFunctor.op).app
      (AddCommGrpCat.of (ULift.{w} ℤ)))

/-- The sheafification unit induces a map from the sheafified pulled-back constant
presheaf to the continuous pushforward of the constant integer sheaf. -/
def face_unitWhisker {n m : SimplexCategory} (φ : n ⟶ m) :
    (presheafToSheaf ((J n).toGrothendieck) AddCommGrpCat.{w}).obj
      ((C.map φ).toFunctor.op ⋙
        ((Functor.const ((C.obj m)ᵒᵖ)).obj (AddCommGrpCat.of (ULift.{w} ℤ)))) ⟶
    ((C.map φ).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{w}
      (J n).toGrothendieck (J m).toGrothendieck).obj
      (constantInteger C J m) :=
  ((sheafificationAdjunction (J n).toGrothendieck AddCommGrpCat.{w}).homEquiv
      ((C.map φ).toFunctor.op ⋙
        ((Functor.const ((C.obj m)ᵒᵖ)).obj (AddCommGrpCat.of (ULift.{w} ℤ))))
      (((C.map φ).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{w}
          (J n).toGrothendieck (J m).toGrothendieck).obj
        (constantInteger C J m))).symm
    (whiskerLeft (C.map φ).toFunctor.op
      ((sheafificationAdjunction (J m).toGrothendieck AddCommGrpCat.{w}).unit.app
        ((Functor.const ((C.obj m)ᵒᵖ)).obj (AddCommGrpCat.of (ULift.{w} ℤ)))))

/-- The comparison `ℤ_n ⟶ f_φ_* ℤ_m` of constant integer sheaves along a simplex operator. -/
def facePushforward_constantInteger_hom {n m : SimplexCategory} (φ : n ⟶ m) :
    constantInteger C J n ⟶
      ((C.map φ).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{w}
        (J n).toGrothendieck (J m).toGrothendieck).obj (constantInteger C J m) :=
  (face_constCompIso C J φ).inv ≫ face_unitWhisker C J φ

/-- The comparison from the pulled-back constant integer sheaf to `ℤ_m`. -/
def facePullback_constantInteger_hom {n m : SimplexCategory} (φ : n ⟶ m) :
    ((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
      (J n).toGrothendieck (J m).toGrothendieck).obj (constantInteger C J n) ⟶
    constantInteger C J m :=
  (((C.map φ).toFunctor.sheafAdjunctionContinuous AddCommGrpCat.{w}
      (J n).toGrothendieck (J m).toGrothendieck).homEquiv
    (constantInteger C J n) (constantInteger C J m)).symm
    (facePushforward_constantInteger_hom C J φ)

/-- The terminal Type-valued sheaf on the degree-`n` stage. -/
abbrev stageTerminalType (n : SimplexCategory) :
    Sheaf ((J n).toGrothendieck) (Type w) :=
  Sheaf.terminal ((J n).toGrothendieck) Types.isTerminalPUnit.{w}

/-- Free abelianization of the terminal Type-sheaf is the constant integer sheaf. -/
def freeTerminalIsoInteger (n : SimplexCategory) :
    (Sheaf.composeAndSheafify ((J n).toGrothendieck) AddCommGrpCat.free).obj
      (stageTerminalType C J n) ≅ constantInteger C J n :=
  (presheafToSheaf ((J n).toGrothendieck) AddCommGrpCat.{w}).mapIso
    ((compConstIso ((C.obj n)ᵒᵖ) AddCommGrpCat.free).symm.app PUnit.{w + 1}) ≪≫
    (constantSheaf ((J n).toGrothendieck) AddCommGrpCat.{w}).mapIso freePUnitIsoInteger

/-- Inverse image along `u_φ` identifies terminal Type-sheaves. -/
def facePullback_terminalTypeIso {n m : SimplexCategory} (φ : n ⟶ m) :
    ((C.map φ).toFunctor.sheafPullback (Type w)
      (J n).toGrothendieck (J m).toGrothendieck).obj (stageTerminalType C J n) ≅
    stageTerminalType C J m :=
  LeftExactAdjunction.inverseImageTerminalIso (toposMap C J φ)
    (Sheaf.isTerminalTerminal ((J n).toGrothendieck) Types.isTerminalPUnit.{w})
    (Sheaf.isTerminalTerminal ((J m).toGrothendieck) Types.isTerminalPUnit.{w})

/-- The generator `1` as a map from the terminal Type-sheaf to the underlying Type-sheaf of `ℤ`. -/
def face_terminalToInteger (n : SimplexCategory) :
    stageTerminalType C J n ⟶
      (sheafForget ((J n).toGrothendieck)).obj (constantInteger C J n) :=
  Sheaf.homEquiv.symm
    { app := fun U ↦
        TypeCat.ofHom fun _ ↦
          (forget AddCommGrpCat.{w}).map
            (((sheafificationAdjunction ((J n).toGrothendieck) AddCommGrpCat.{w}).unit.app
              ((Functor.const ((C.obj n)ᵒᵖ)).obj
                (AddCommGrpCat.of (ULift.{w} ℤ)))).app U)
            (ULift.up (1 : ℤ))
      naturality := by
        intro U V f
        ext x
        exact congrArg (fun g => g (ULift.up (1 : ℤ)))
          (((sheafificationAdjunction ((J n).toGrothendieck) AddCommGrpCat.{w}).unit.app
            ((Functor.const ((C.obj n)ᵒᵖ)).obj
              (AddCommGrpCat.of (ULift.{w} ℤ)))).naturality f) }

/-- Continuous pushforward commutes with forgetting abelian sheaves to Type-valued sheaves. -/
def face_pushforwardForgetIso {n m : SimplexCategory} (φ : n ⟶ m)
    (G : Sheaf ((J m).toGrothendieck) AddCommGrpCat.{w}) :
    ((C.map φ).toFunctor.sheafPushforwardContinuous (Type w)
      (J n).toGrothendieck (J m).toGrothendieck).obj
      ((sheafForget ((J m).toGrothendieck)).obj G) ≅
    (sheafForget ((J n).toGrothendieck)).obj
      (((C.map φ).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{w}
        (J n).toGrothendieck (J m).toGrothendieck).obj G) where
  hom := Sheaf.homEquiv.symm (𝟙 _)
  inv := Sheaf.homEquiv.symm (𝟙 _)
  hom_inv_id := by
    apply Sheaf.hom_ext
    exact Category.id_comp _
  inv_hom_id := by
    apply Sheaf.hom_ext
    exact Category.id_comp _

/-- The Type-sheaf map `⊤_n ⟶ forget (f_φ_* f_φ⁻¹ ℤ_n)` sending the point to `1`. -/
def face_terminalToPushforwardInteger {n m : SimplexCategory} (φ : n ⟶ m) :
    stageTerminalType C J n ⟶
      ((C.map φ).toFunctor.sheafPushforwardContinuous (Type w)
        (J n).toGrothendieck (J m).toGrothendieck).obj
        ((sheafForget ((J m).toGrothendieck)).obj
          (((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
            (J n).toGrothendieck (J m).toGrothendieck).obj (constantInteger C J n))) :=
  face_terminalToInteger C J n ≫
    (sheafForget ((J n).toGrothendieck)).map
      (((C.map φ).toFunctor.sheafAdjunctionContinuous AddCommGrpCat.{w}
        (J n).toGrothendieck (J m).toGrothendieck).unit.app (constantInteger C J n)) ≫
    (face_pushforwardForgetIso C J φ
      (((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
        (J n).toGrothendieck (J m).toGrothendieck).obj (constantInteger C J n))).inv

/-- The Type-sheaf map `⊤_m ⟶ forget (f_φ⁻¹ ℤ_n)` corresponding to the generator `1`. -/
def face_terminalToPullbackInteger {n m : SimplexCategory} (φ : n ⟶ m) :
    stageTerminalType C J m ⟶
      (sheafForget ((J m).toGrothendieck)).obj
        (((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
          (J n).toGrothendieck (J m).toGrothendieck).obj (constantInteger C J n)) :=
  (facePullback_terminalTypeIso C J φ).inv ≫
    (((C.map φ).toFunctor.sheafAdjunctionContinuous (Type w)
      (J n).toGrothendieck (J m).toGrothendieck).homEquiv
      (stageTerminalType C J n)
      ((sheafForget ((J m).toGrothendieck)).obj
        (((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
          (J n).toGrothendieck (J m).toGrothendieck).obj (constantInteger C J n)))).symm
      (face_terminalToPushforwardInteger C J φ)

/-- The comparison `ℤ_m ⟶ f_φ⁻¹ ℤ_n` of constant integer sheaves along a simplex operator. -/
def facePullback_constantInteger_inv {n m : SimplexCategory} (φ : n ⟶ m) :
    constantInteger C J m ⟶
      ((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
        (J n).toGrothendieck (J m).toGrothendieck).obj (constantInteger C J n) :=
  (freeTerminalIsoInteger C J m).inv ≫
    ((Sheaf.adjunction ((J m).toGrothendieck) AddCommGrpCat.adj).homEquiv
      (stageTerminalType C J m)
      (((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
        (J n).toGrothendieck (J m).toGrothendieck).obj (constantInteger C J n))).symm
      (face_terminalToPullbackInteger C J φ)

/-- The forward constant-sheaf comparison followed by the reverse comparison is the
identity on the pulled-back constant integer sheaf. -/
theorem facePullback_constantInteger_hom_inv_id {n m : SimplexCategory} (φ : n ⟶ m) :
    facePullback_constantInteger_hom C J φ ≫ facePullback_constantInteger_inv C J φ =
      𝟙 (((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
        (J n).toGrothendieck (J m).toGrothendieck).obj (constantInteger C J n)) :=
  sorry

/-- The reverse constant-sheaf comparison followed by the forward comparison is the
identity on the constant integer sheaf. -/
theorem facePullback_constantInteger_inv_hom_id {n m : SimplexCategory} (φ : n ⟶ m) :
    facePullback_constantInteger_inv C J φ ≫ facePullback_constantInteger_hom C J φ =
      𝟙 (constantInteger C J m) :=
  sorry

/-- The comparison of pulled-back constant integer sheaves along a simplex operator. -/
def facePullback_constantIntegerIso {n m : SimplexCategory} (φ : n ⟶ m) :
    ((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
      (J n).toGrothendieck (J m).toGrothendieck).obj (constantInteger C J n) ≅
    constantInteger C J m where
  hom := facePullback_constantInteger_hom C J φ
  inv := facePullback_constantInteger_inv C J φ
  hom_inv_id := facePullback_constantInteger_hom_inv_id C J φ
  inv_hom_id := facePullback_constantInteger_inv_hom_id C J φ

/-- The comparison `f_φ⁻¹ ℤ_n ⟶ ℤ_m` is an isomorphism of constant integer sheaves. -/
instance facePullback_constantInteger_hom_isIso {n m : SimplexCategory} (φ : n ⟶ m) :
    IsIso (facePullback_constantInteger_hom C J φ) :=
  (facePullback_constantIntegerIso C J φ).isIso_hom

/-- The forward comparison of `facePullback_constantIntegerIso` is
`facePullback_constantInteger_hom`. -/
theorem facePullback_constantIntegerIso_hom_eq {n m : SimplexCategory} (φ : n ⟶ m) :
    (facePullback_constantIntegerIso C J φ).hom =
      facePullback_constantInteger_hom C J φ :=
  rfl

/-- The reverse comparison of `facePullback_constantIntegerIso` is
`facePullback_constantInteger_inv`. -/
theorem facePullback_constantIntegerIso_inv_eq {n m : SimplexCategory} (φ : n ⟶ m) :
    (facePullback_constantIntegerIso C J φ).inv =
      facePullback_constantInteger_inv C J φ :=
  rfl

/-- The comparison `ℤ_n ⟶ g_n⁻¹ ℤ` of constant integer sheaves along `ofStage C n`. -/
def ofStage_constantInteger_hom (n : SimplexCategory) :
    constantInteger C J n ⟶
      (stageRestrict C J AddCommGrpCat.{w} n).obj
        (constantIntegerSheaf (topology C J)) :=
  ((sheafificationAdjunction (J n).toGrothendieck AddCommGrpCat.{w}).homEquiv
      ((Functor.const _).obj (AddCommGrpCat.of (ULift.{w} ℤ)))
      ((stageRestrict C J AddCommGrpCat.{w} n).obj
        (constantIntegerSheaf (topology C J)))).symm
    ((constCompWhiskeringLeftIso (C.obj n)ᵒᵖ (ofStage C n).op).inv.app
      (AddCommGrpCat.of (ULift.{w} ℤ)) ≫
      whiskerLeft (ofStage C n).op
        ((sheafificationAdjunction (topology C J) AddCommGrpCat.{w}).unit.app
          ((Functor.const _).obj (AddCommGrpCat.of (ULift.{w} ℤ)))))

/-- The structure map `g_{m!} ℤ ⟶ g_{n!} ℤ` induced by a simplex operator `φ : n ⟶ m`. -/
def lowerShriekConstant_map {n m : SimplexCategory} (φ : n ⟶ m) :
    (abelianLowerShriek C J m).obj (constantInteger C J m) ⟶
      (abelianLowerShriek C J n).obj (constantInteger C J n) :=
  ((abelianLowerShriek_adjunction C J m).homEquiv
      (constantInteger C J m)
      ((abelianLowerShriek C J n).obj (constantInteger C J n))).symm
    (facePullback_constantInteger_inv C J φ ≫
      abelianLowerShriek_component C J φ (constantInteger C J n))

/-- Identity simplex operators induce identity structure maps of `n ↦ g_{n!} ℤ`. -/
theorem lowerShriekConstant_map_id (n : SimplexCategory) :
    lowerShriekConstant_map C J (𝟙 n) =
      𝟙 ((abelianLowerShriek C J n).obj (constantInteger C J n)) :=
  sorry

/-- Structure maps of `n ↦ g_{n!} ℤ` are functorial in simplex operators. -/
theorem lowerShriekConstant_map_comp {l n m : SimplexCategory}
    (ψ : l ⟶ n) (φ : n ⟶ m) :
    lowerShriekConstant_map C J (ψ ≫ φ) =
      lowerShriekConstant_map C J φ ≫ lowerShriekConstant_map C J ψ :=
  sorry

/-- Opposite identity operators act as identity maps of `n ↦ g_{n!} ℤ`. -/
private theorem lowerShriekConstant_map_id_op (n : SimplexCategoryᵒᵖ) :
    lowerShriekConstant_map C J (𝟙 n.unop) =
      𝟙 ((abelianLowerShriek C J n.unop).obj (constantInteger C J n.unop)) :=
  lowerShriekConstant_map_id C J n.unop

/-- Opposite composition of simplex operators acts as composition of structure maps. -/
private theorem lowerShriekConstant_map_comp_op {n m p : SimplexCategoryᵒᵖ}
    (f : n ⟶ m) (g : m ⟶ p) :
    lowerShriekConstant_map C J (f ≫ g).unop =
      lowerShriekConstant_map C J f.unop ≫ lowerShriekConstant_map C J g.unop :=
  lowerShriekConstant_map_comp C J g.unop f.unop

/-- The simplicial abelian sheaf `n ↦ g_{n!} ℤ` on the total site. -/
def lowerShriekConstant :
    SimplicialObject (Sheaf (topology C J) AddCommGrpCat.{w}) where
  obj n := (abelianLowerShriek C J n.unop).obj (constantInteger C J n.unop)
  map f := lowerShriekConstant_map C J f.unop
  map_id := by exact lowerShriekConstant_map_id_op C J
  map_comp := by exact lowerShriekConstant_map_comp_op C J

/-- The value of `lowerShriekConstant` at `n` is `g_{n!} ℤ`. -/
theorem lowerShriekConstant_obj (n : SimplexCategory) :
    (lowerShriekConstant C J).obj (op n) =
      (abelianLowerShriek C J n).obj (constantInteger C J n) :=
  rfl

/-- The face map `d_i : g_{(n+1)!} ℤ ⟶ g_{n!} ℤ`. -/
def face (n : ℕ) (i : Fin (n + 2)) :
    (lowerShriekConstant C J).obj (op ⦋n + 1⦌) ⟶
      (lowerShriekConstant C J).obj (op ⦋n⦌) :=
  (lowerShriekConstant C J).δ i

/-- The face map `face i` is the simplicial operator `δ i`. -/
theorem face_eq (n : ℕ) (i : Fin (n + 2)) :
    face C J n i = (lowerShriekConstant C J).δ i :=
  rfl

/-- The component of the augmentation `g_{n!} ℤ ⟶ ℤ` at a simplex `n`. -/
def augmented_hom_app (n : SimplexCategoryᵒᵖ) :
    (lowerShriekConstant C J).obj n ⟶ constantIntegerSheaf (topology C J) :=
  ((abelianLowerShriek_adjunction C J n.unop).homEquiv
      (constantInteger C J n.unop) (constantIntegerSheaf (topology C J))).symm
    (ofStage_constantInteger_hom C J n.unop)

/-- Naturality of the degreewise augmentation `g_{n!} ℤ ⟶ ℤ`. -/
theorem augmented_hom_naturality :
    ∀ ⦃n m : SimplexCategoryᵒᵖ⦄ (f : n ⟶ m),
      (lowerShriekConstant C J).map f ≫ augmented_hom_app C J m =
        augmented_hom_app C J n ≫
          ((SimplicialObject.const _).obj
            (constantIntegerSheaf (topology C J))).map f :=
  sorry

/-- The natural transformation `n ↦ g_{n!} ℤ ⟶ const ℤ`. -/
def augmented_hom :
    lowerShriekConstant C J ⟶
      (SimplicialObject.const _).obj (constantIntegerSheaf (topology C J)) where
  app := augmented_hom_app C J
  naturality := augmented_hom_naturality C J

/-- The augmented simplicial object of `g_{n!} ℤ` over the constant sheaf `ℤ`. -/
def augmented :
    SimplicialObject.Augmented (Sheaf (topology C J) AddCommGrpCat.{w}) where
  left := lowerShriekConstant C J
  right := constantIntegerSheaf (topology C J)
  hom := augmented_hom C J

variable [HasSheafify (topology C J) AddCommGrpCat.{w}]

/-- The alternating-face chain complex `… → g_{2!} ℤ → g_{1!} ℤ → g_{0!} ℤ`. -/
abbrev complex : ChainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℕ :=
  (alternatingFaceMapComplex _).obj (SimplicialObject.Augmented.drop.obj (augmented C J))

/-- Degree `n` of `complex C J` is the abelian sheaf `g_{n!} ℤ`. -/
theorem complex_X (n : ℕ) :
    (complex C J).X n =
      (abelianLowerShriek C J ⦋n⦌).obj (constantInteger C J ⦋n⦌) :=
  rfl

/-- Differentials of `complex C J` are the alternating sums of face maps. -/
theorem complex_d_eq (n : ℕ) :
    (complex C J).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • face C J n i :=
  AlternatingFaceMapComplex.obj_d_eq (lowerShriekConstant C J) n

/-- The canonical chain-map augmentation from `complex C J` to the constant sheaf `ℤ`
concentrated in degree zero. -/
def augmentation :
    complex C J ⟶ (ChainComplex.single₀ _).obj (constantIntegerSheaf (topology C J)) :=
  AlternatingFaceMapComplex.ε.app (augmented C J)

/-- The degree-zero component of `augmentation C J` is the simplicial augmentation at `⦋0⦌`. -/
theorem augmentation_f_zero :
    (augmentation C J).f 0 = (augmented C J).hom.app (op ⦋0⦌) :=
  AlternatingFaceMapComplex.ε_app_f_zero (augmented C J)


end CategoryTheory.SimplicialSites

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget AddCommGrpCat.{w})]

/-- The canonically augmented alternating-face complex of lower-shriek constant
integer sheaves resolves the constant integer sheaf on the total site. -/
instance augmentation_quasiIso :
    QuasiIso
      (augmentation C J :
        complex C J ⟶
          (ChainComplex.single₀ _).obj (constantIntegerSheaf (topology C J))) :=
  sorry

end CategoryTheory.SimplicialSites

