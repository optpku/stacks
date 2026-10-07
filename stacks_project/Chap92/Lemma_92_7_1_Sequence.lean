module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import stacks_project.Chap92.Lemma_92_7_1_Omega
public import stacks_project.Chap92.«92_7_0_2_Maps»

/-!
# The sheaf sequence of naive differentials on `C_{C/B/A}`

This leaf owns the inverse images of `omegaSheaf` along `u1`, `u2`, `u3`, the tensor
`g1⁻¹Ω₁ ⊗_{underline{B}} underline{C}`, the two comparison maps, the identification
`Ω[Q ⁄ P] ⊗ C ≃ Ω[Q ⊗[P] B ⁄ B] ⊗ C`, and the resulting short complex of
`underline{C}`-modules.
-/

@[expose] public section

open CategoryTheory Opposite
open CommAlgCat.Over.Polynomial.Site
open scoped TensorProduct

noncomputable section

universe u

namespace RingedSite.Cotangent.PolynomialTriple

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- Inverse image `g1⁻¹ Ω₁`, obtained by precomposing `omegaSheaf A B` with `u1`. -/
def inverseImageOmega1 : PolynomialTriple A B C ⥤ _root_.ModuleCat.{u} B :=
  forgetToBase A B C ⋙ omegaSheafCov A B

/-- Inverse image `g2⁻¹ Ω₂`, obtained by precomposing `omegaSheaf A C` with `u2`. -/
def inverseImageOmega2 : PolynomialTriple A B C ⥤ _root_.ModuleCat.{u} C :=
  forgetToOverA A B C ⋙ omegaSheafCov A C

/-- Inverse image `g3⁻¹ Ω₃`, obtained by precomposing `omegaSheaf B C` with `u3`. -/
def inverseImageOmega3 : PolynomialTriple A B C ⥤ _root_.ModuleCat.{u} C :=
  forgetToOverB A B C ⋙ omegaSheafCov B C

/-- `inverseImageOmega1` evaluates at a triple to the naive differentials of `P ⟶ B`. -/
theorem inverseImageOmega1_obj (X : PolynomialTriple A B C) :
    (inverseImageOmega1 A B C).obj X = omegaSheafObj (forgetToBaseObj X) :=
  sorry

/-- `inverseImageOmega2` evaluates at a triple to the naive differentials of `Q ⟶ C` over `A`. -/
theorem inverseImageOmega2_obj (X : PolynomialTriple A B C) :
    (inverseImageOmega2 A B C).obj X = omegaSheafObj (forgetToOverAObj X) :=
  sorry

/-- `inverseImageOmega3` evaluates at a triple to the naive differentials of `Q ⊗[P] B ⟶ C`. -/
theorem inverseImageOmega3_obj (X : PolynomialTriple A B C) :
    (inverseImageOmega3 A B C).obj X = omegaSheafObj (tensorOverBase X) :=
  sorry

/-- Inverse image along `g1` is precomposition with `u1`. -/
theorem inverseImageOmega1_eq_u1 :
    inverseImageOmega1 A B C =
      opOp (PolynomialTriple A B C) ⋙ (u1 A B C).op ⋙ omegaSheaf A B :=
  sorry

/-- Inverse image along `g2` is precomposition with `u2`. -/
theorem inverseImageOmega2_eq_u2 :
    inverseImageOmega2 A B C =
      opOp (PolynomialTriple A B C) ⋙ (u2 A B C).op ⋙ omegaSheaf A C :=
  sorry

/-- Inverse image along `g3` is precomposition with `u3`. -/
theorem inverseImageOmega3_eq_u3 :
    inverseImageOmega3 A B C =
      opOp (PolynomialTriple A B C) ⋙ (u3 A B C).op ⋙ omegaSheaf B C :=
  sorry

/-- The value of `g1⁻¹Ω₁ ⊗_{underline{B}} underline{C}` on a triple. -/
def tensorOmega1Obj (X : PolynomialTriple A B C) : _root_.ModuleCat.{u} C :=
  _root_.ModuleCat.of C (C ⊗[B] ((inverseImageOmega1 A B C).obj X : Type u))

/-- The map of `g1⁻¹Ω₁ ⊗_{underline{B}} underline{C}` induced by a morphism of triples. -/
def tensorOmega1Map {X Y : PolynomialTriple A B C} (f : X ⟶ Y) :
    tensorOmega1Obj A B C X ⟶ tensorOmega1Obj A B C Y :=
  _root_.ModuleCat.ofHom (((inverseImageOmega1 A B C).map f).hom.baseChange C)

/-- Identity morphisms tensor to identity morphisms over `C`. -/
theorem tensorOmega1Map_id (X : PolynomialTriple A B C) :
    tensorOmega1Map A B C (𝟙 X) = 𝟙 (tensorOmega1Obj A B C X) :=
  sorry

/-- Composition of triples tensors to composition over `C`. -/
theorem tensorOmega1Map_comp {X Y Z : PolynomialTriple A B C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    tensorOmega1Map A B C (f ≫ g) = tensorOmega1Map A B C f ≫ tensorOmega1Map A B C g :=
  sorry

/-- The sheaf `g1⁻¹Ω₁ ⊗_{underline{B}} underline{C}` on `C_{C/B/A}`. -/
def tensorOmega1 : PolynomialTriple A B C ⥤ _root_.ModuleCat.{u} C where
  obj := tensorOmega1Obj A B C
  map f := tensorOmega1Map A B C f
  map_id X := tensorOmega1Map_id A B C X
  map_comp f g := tensorOmega1Map_comp A B C f g

/-- Objects of `tensorOmega1` are the tensors over `B` of `g1⁻¹Ω₁` with `C`. -/
theorem tensorOmega1_obj (X : PolynomialTriple A B C) :
    (tensorOmega1 A B C).obj X = tensorOmega1Obj A B C X :=
  sorry

/-- `tensorOmega1` is extension of scalars of `inverseImageOmega1` along `B ⟶ C`. -/
theorem tensorOmega1_eq_extendScalars :
    tensorOmega1 A B C =
      inverseImageOmega1 A B C ⋙ _root_.ModuleCat.extendScalars (algebraMap B C) :=
  sorry

/-- The tower `A ⟶ P ⟶ Q` on a triple, using `algebraAQ`. -/
theorem isScalarTowerAPQ (X : PolynomialTriple A B C) [Algebra A X.Q] :
    IsScalarTower A X.P X.Q :=
  sorry

/-- The tower `P ⟶ B ⟶ C` on a triple, using `algebraPB` and `algebraPC`. -/
theorem isScalarTowerPBC (X : PolynomialTriple A B C) [Algebra X.P B] [Algebra X.P C] :
    IsScalarTower X.P B C :=
  sorry

/-- The `Q`-algebra structure on `C` from the structure morphism of the triple. -/
@[reducible] def algebraQC (X : PolynomialTriple A B C) : Algebra X.Q C :=
  RingHom.toAlgebra (toCRingHom X)

/-- Unfolding `algebraQC` recovers the underlying ring map `Q ⟶ C`. -/
theorem algebraQC_eq (X : PolynomialTriple A B C) :
    algebraQC A B C X = RingHom.toAlgebra (toCRingHom X) :=
  sorry

/-- The tower `P ⟶ Q ⟶ C` on a triple. -/
theorem isScalarTowerPQC (X : PolynomialTriple A B C) [Algebra X.Q C] [Algebra X.P C] :
    IsScalarTower X.P X.Q C :=
  sorry

/-- The tower `A ⟶ Q ⟶ C` on a triple. -/
theorem isScalarTowerAQC (X : PolynomialTriple A B C) [Algebra A X.Q] [Algebra X.Q C] :
    IsScalarTower A X.Q C :=
  sorry

/-- The `B`-algebra structure on `Q ⊗[P] B` used by the triple. -/
@[reducible] def algebraTensorRight (X : PolynomialTriple A B C) [Algebra X.P B] :
    Algebra B (X.Q ⊗[X.P] B) :=
  Algebra.TensorProduct.rightAlgebra

/-- The algebra map `Q ⊗[P] B ⟶ C`. -/
@[reducible] def algebraTensorC (X : PolynomialTriple A B C)
    [Algebra X.P B] [Algebra X.P C] [Algebra B (X.Q ⊗[X.P] B)] :
    Algebra (X.Q ⊗[X.P] B) C :=
  RingHom.toAlgebra (tensorToCWith X).toRingHom

/-- The tower `P ⟶ B ⟶ Q ⊗[P] B`. -/
theorem isScalarTower_PB_tensor (X : PolynomialTriple A B C)
    [Algebra X.P B] [Algebra B (X.Q ⊗[X.P] B)] :
    IsScalarTower X.P B (X.Q ⊗[X.P] B) :=
  sorry

/-- The pushout instance `Algebra.IsPushout P B Q (Q ⊗[P] B)`. -/
theorem isPushout_tensor (X : PolynomialTriple A B C)
    [Algebra X.P B] [Algebra B (X.Q ⊗[X.P] B)]
    [IsScalarTower X.P B (X.Q ⊗[X.P] B)] :
    Algebra.IsPushout X.P B X.Q (X.Q ⊗[X.P] B) :=
  sorry

/-- The tower `Q ⟶ Q ⊗[P] B ⟶ C`. -/
theorem isScalarTower_tensorC (X : PolynomialTriple A B C)
    [Algebra X.P B] [Algebra (X.Q ⊗[X.P] B) C] [Algebra X.Q C] :
    IsScalarTower X.Q (X.Q ⊗[X.P] B) C :=
  sorry

/-- The left map of the sheaf sequence at a triple, in the presence of the induced algebras. -/
def toOmega2AppWith (X : PolynomialTriple A B C)
    [Algebra X.P B] [Algebra A X.Q] [Algebra X.P C] [Algebra X.Q C]
    [IsScalarTower A X.P X.Q] [IsScalarTower X.P B C]
    [IsScalarTower X.P X.Q C] [IsScalarTower A X.Q C] :
    _root_.ModuleCat.of C (C ⊗[B] (B ⊗[X.P] KaehlerDifferential A X.P)) ⟶
      _root_.ModuleCat.of C (C ⊗[X.Q] KaehlerDifferential A X.Q) :=
  _root_.ModuleCat.ofHom
    ((KaehlerDifferential.mapBaseChange A X.P X.Q).baseChange C ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange
          X.P X.Q C C (KaehlerDifferential A X.P)).symm.toLinearMap ∘ₗ
        (TensorProduct.AlgebraTensorModule.cancelBaseChange
          X.P B C C (KaehlerDifferential A X.P)).toLinearMap)

/-- The left map of the sheaf sequence, evaluated at a triple. -/
def toOmega2App (X : PolynomialTriple A B C) :
    (tensorOmega1 A B C).obj X ⟶ (inverseImageOmega2 A B C).obj X :=
  @toOmega2AppWith A B C _ _ _ _ _ _ _ X (algebraPB X) (algebraAQ X) (algebraPC X)
    (algebraQC A B C X)
    (@isScalarTowerAPQ A B C _ _ _ _ _ _ _ X (algebraAQ X))
    (@isScalarTowerPBC A B C _ _ _ _ _ _ _ X (algebraPB X) (algebraPC X))
    (@isScalarTowerPQC A B C _ _ _ _ _ _ _ X (algebraQC A B C X) (algebraPC X))
    (@isScalarTowerAQC A B C _ _ _ _ _ _ _ X (algebraAQ X) (algebraQC A B C X))

/-- `toOmega2App` is the tensored Jacobi–Zariski map `mapBaseChange`. -/
theorem toOmega2App_eq (X : PolynomialTriple A B C) :
    toOmega2App A B C X =
      @toOmega2AppWith A B C _ _ _ _ _ _ _ X (algebraPB X) (algebraAQ X) (algebraPC X)
        (algebraQC A B C X)
        (@isScalarTowerAPQ A B C _ _ _ _ _ _ _ X (algebraAQ X))
        (@isScalarTowerPBC A B C _ _ _ _ _ _ _ X (algebraPB X) (algebraPC X))
        (@isScalarTowerPQC A B C _ _ _ _ _ _ _ X (algebraQC A B C X) (algebraPC X))
        (@isScalarTowerAQC A B C _ _ _ _ _ _ _ X (algebraAQ X) (algebraQC A B C X)) :=
  sorry

/-- Naturality of the left map of the sheaf sequence. -/
theorem toOmega2_naturality {X Y : PolynomialTriple A B C} (f : X ⟶ Y) :
    tensorOmega1Map A B C f ≫ toOmega2App A B C Y =
      toOmega2App A B C X ≫ (inverseImageOmega2 A B C).map f :=
  sorry

/-- The left map `g1⁻¹Ω₁ ⊗_{underline{B}} underline{C} ⟶ g2⁻¹Ω₂` of the sheaf sequence. -/
def toOmega2 : tensorOmega1 A B C ⟶ inverseImageOmega2 A B C where
  app := toOmega2App A B C
  naturality _ _ f := toOmega2_naturality A B C f

/-- The `00RV` identification `Ω[Q ⁄ P] ⊗[Q] C ≃ Ω[Q ⊗[P] B ⁄ B] ⊗ C` at a triple,
in the presence of the pushout algebras. -/
def omega3IsoWith (X : PolynomialTriple A B C)
    [Algebra X.P B] [Algebra B (X.Q ⊗[X.P] B)]
    [IsScalarTower X.P B (X.Q ⊗[X.P] B)]
    [Algebra.IsPushout X.P B X.Q (X.Q ⊗[X.P] B)]
    [Algebra X.Q C] [Algebra (X.Q ⊗[X.P] B) C]
    [IsScalarTower X.Q (X.Q ⊗[X.P] B) C] :
    _root_.ModuleCat.of C (C ⊗[X.Q] KaehlerDifferential X.P X.Q) ≅
      _root_.ModuleCat.of C
        (C ⊗[X.Q ⊗[X.P] B] KaehlerDifferential B (X.Q ⊗[X.P] B)) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange
      X.Q (X.Q ⊗[X.P] B) C C (KaehlerDifferential X.P X.Q)).symm.toModuleIso ≪≫
    LinearEquiv.toModuleIso
      (LinearEquiv.ofLinear
        ((KaehlerDifferential.tensorKaehlerEquiv X.P B X.Q (X.Q ⊗[X.P] B)).toLinearMap.baseChange C)
        ((KaehlerDifferential.tensorKaehlerEquiv
            X.P B X.Q (X.Q ⊗[X.P] B)).symm.toLinearMap.baseChange C)
        sorry sorry)

/-- The `00RV` identification at a triple. -/
def omega3Iso (X : PolynomialTriple A B C) :=
  @omega3IsoWith A B C _ _ _ _ _ _ _ X (algebraPB X)
    (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X))
    (@isScalarTower_PB_tensor A B C _ _ _ _ _ _ _ X (algebraPB X)
      (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X)))
    (@isPushout_tensor A B C _ _ _ _ _ _ _ X (algebraPB X)
      (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X))
      (@isScalarTower_PB_tensor A B C _ _ _ _ _ _ _ X (algebraPB X)
        (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X))))
    (algebraQC A B C X)
    (@algebraTensorC A B C _ _ _ _ _ _ _ X (algebraPB X) (algebraPC X)
      (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X)))
    (@isScalarTower_tensorC A B C _ _ _ _ _ _ _ X (algebraPB X)
      (@algebraTensorC A B C _ _ _ _ _ _ _ X (algebraPB X) (algebraPC X)
        (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X)))
      (algebraQC A B C X))

/-- Applying `omega3Iso` recovers the base change of `tensorKaehlerEquiv`. -/
theorem omega3Iso_eq (X : PolynomialTriple A B C) :
    omega3Iso A B C X =
      @omega3IsoWith A B C _ _ _ _ _ _ _ X (algebraPB X)
        (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X))
        (@isScalarTower_PB_tensor A B C _ _ _ _ _ _ _ X (algebraPB X)
          (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X)))
        (@isPushout_tensor A B C _ _ _ _ _ _ _ X (algebraPB X)
          (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X))
          (@isScalarTower_PB_tensor A B C _ _ _ _ _ _ _ X (algebraPB X)
            (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X))))
        (algebraQC A B C X)
        (@algebraTensorC A B C _ _ _ _ _ _ _ X (algebraPB X) (algebraPC X)
          (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X)))
        (@isScalarTower_tensorC A B C _ _ _ _ _ _ _ X (algebraPB X)
          (@algebraTensorC A B C _ _ _ _ _ _ _ X (algebraPB X) (algebraPC X)
            (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X)))
          (algebraQC A B C X)) :=
  sorry

/-- The right map of the sheaf sequence at a triple, in the presence of the induced algebras. -/
def toOmega3AppWith (X : PolynomialTriple A B C)
    [Algebra A X.Q] [Algebra X.Q C] [Algebra X.P C]
    [IsScalarTower A X.P X.Q] [IsScalarTower A X.Q C]
    [IsScalarTower X.P X.Q C]
    [Algebra X.P B] [Algebra B (X.Q ⊗[X.P] B)]
    [IsScalarTower X.P B (X.Q ⊗[X.P] B)]
    [Algebra.IsPushout X.P B X.Q (X.Q ⊗[X.P] B)]
    [Algebra (X.Q ⊗[X.P] B) C] [IsScalarTower X.Q (X.Q ⊗[X.P] B) C] :
    _root_.ModuleCat.of C (C ⊗[X.Q] KaehlerDifferential A X.Q) ⟶
      _root_.ModuleCat.of C
        (C ⊗[X.Q ⊗[X.P] B] KaehlerDifferential B (X.Q ⊗[X.P] B)) :=
  _root_.ModuleCat.ofHom ((KaehlerDifferential.map A X.P X.Q X.Q).baseChange C) ≫
    (omega3IsoWith A B C X).hom

/-- The right map of the sheaf sequence, evaluated at a triple. -/
def toOmega3App (X : PolynomialTriple A B C) :
    (inverseImageOmega2 A B C).obj X ⟶ (inverseImageOmega3 A B C).obj X :=
  @toOmega3AppWith A B C _ _ _ _ _ _ _ X (algebraAQ X) (algebraQC A B C X) (algebraPC X)
    (@isScalarTowerAPQ A B C _ _ _ _ _ _ _ X (algebraAQ X))
    (@isScalarTowerAQC A B C _ _ _ _ _ _ _ X (algebraAQ X) (algebraQC A B C X))
    (@isScalarTowerPQC A B C _ _ _ _ _ _ _ X (algebraQC A B C X) (algebraPC X))
    (algebraPB X)
    (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X))
    (@isScalarTower_PB_tensor A B C _ _ _ _ _ _ _ X (algebraPB X)
      (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X)))
    (@isPushout_tensor A B C _ _ _ _ _ _ _ X (algebraPB X)
      (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X))
      (@isScalarTower_PB_tensor A B C _ _ _ _ _ _ _ X (algebraPB X)
        (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X))))
    (@algebraTensorC A B C _ _ _ _ _ _ _ X (algebraPB X) (algebraPC X)
      (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X)))
    (@isScalarTower_tensorC A B C _ _ _ _ _ _ _ X (algebraPB X)
      (@algebraTensorC A B C _ _ _ _ _ _ _ X (algebraPB X) (algebraPC X)
        (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X)))
      (algebraQC A B C X))

/-- `toOmega3App` is the tensored Jacobi–Zariski map followed by `omega3Iso`. -/
theorem toOmega3App_eq (X : PolynomialTriple A B C) :
    toOmega3App A B C X =
      @toOmega3AppWith A B C _ _ _ _ _ _ _ X (algebraAQ X) (algebraQC A B C X) (algebraPC X)
        (@isScalarTowerAPQ A B C _ _ _ _ _ _ _ X (algebraAQ X))
        (@isScalarTowerAQC A B C _ _ _ _ _ _ _ X (algebraAQ X) (algebraQC A B C X))
        (@isScalarTowerPQC A B C _ _ _ _ _ _ _ X (algebraQC A B C X) (algebraPC X))
        (algebraPB X)
        (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X))
        (@isScalarTower_PB_tensor A B C _ _ _ _ _ _ _ X (algebraPB X)
          (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X)))
        (@isPushout_tensor A B C _ _ _ _ _ _ _ X (algebraPB X)
          (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X))
          (@isScalarTower_PB_tensor A B C _ _ _ _ _ _ _ X (algebraPB X)
            (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X))))
        (@algebraTensorC A B C _ _ _ _ _ _ _ X (algebraPB X) (algebraPC X)
          (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X)))
        (@isScalarTower_tensorC A B C _ _ _ _ _ _ _ X (algebraPB X)
          (@algebraTensorC A B C _ _ _ _ _ _ _ X (algebraPB X) (algebraPC X)
            (@algebraTensorRight A B C _ _ _ _ _ _ _ X (algebraPB X)))
          (algebraQC A B C X)) :=
  sorry

/-- Naturality of the right map of the sheaf sequence. -/
theorem toOmega3_naturality {X Y : PolynomialTriple A B C} (f : X ⟶ Y) :
    (inverseImageOmega2 A B C).map f ≫ toOmega3App A B C Y =
      toOmega3App A B C X ≫ (inverseImageOmega3 A B C).map f :=
  sorry

/-- The right map `g2⁻¹Ω₂ ⟶ g3⁻¹Ω₃` of the sheaf sequence. -/
def toOmega3 : inverseImageOmega2 A B C ⟶ inverseImageOmega3 A B C where
  app := toOmega3App A B C
  naturality _ _ f := toOmega3_naturality A B C f

/-- The composite of the two maps in the sheaf sequence is zero. -/
theorem omegaSequence_zero : toOmega2 A B C ≫ toOmega3 A B C = 0 :=
  sorry

/-- The canonical sequence
`g1⁻¹Ω₁ ⊗_{underline{B}} underline{C} ⟶ g2⁻¹Ω₂ ⟶ g3⁻¹Ω₃`
of sheaves of `underline{C}`-modules on `C_{C/B/A}`. -/
def omegaSequence : ShortComplex (PolynomialTriple A B C ⥤ _root_.ModuleCat.{u} C) :=
  ShortComplex.mk (toOmega2 A B C) (toOmega3 A B C) (omegaSequence_zero A B C)

/-- Unfolding `omegaSequence` recovers the short complex on `toOmega2` and `toOmega3`. -/
theorem omegaSequence_eq :
    omegaSequence A B C =
      ShortComplex.mk (toOmega2 A B C) (toOmega3 A B C) (omegaSequence_zero A B C) :=
  sorry

/-- The composite of the evaluated maps at a triple is zero. -/
theorem omegaSequence_app_zero (X : PolynomialTriple A B C) :
    toOmega2App A B C X ≫ toOmega3App A B C X = 0 :=
  sorry

/-- Evaluation of the sheaf sequence at a triple `(P ⟶ B, Q ⟶ C)`. -/
def omegaSequence_app (X : PolynomialTriple A B C) : ShortComplex (_root_.ModuleCat.{u} C) :=
  ShortComplex.mk (toOmega2App A B C X) (toOmega3App A B C X) (omegaSequence_app_zero A B C X)

/-- Unfolding `omegaSequence_app` recovers the pointwise short complex. -/
theorem omegaSequence_app_eq (X : PolynomialTriple A B C) :
    omegaSequence_app A B C X =
      ShortComplex.mk (toOmega2App A B C X) (toOmega3App A B C X)
        (omegaSequence_app_zero A B C X) :=
  sorry

/-- The sheaf sequence is short exact on each object of `C_{C/B/A}`. -/
theorem omegaSequence_app_shortExact (X : PolynomialTriple A B C) :
    (omegaSequence_app A B C X).ShortExact :=
  sorry

end RingedSite.Cotangent.PolynomialTriple
