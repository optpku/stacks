module

public import ReasLib.AlgebraicGeometry.ChowMotive
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory.Linear
public import ReasLib.CategoryTheory.Idempotents.Karoubi.Linear
public import ReasLib.AlgebraicGeometry.Correspondence.ProjectiveLine
public import ReasLib.AlgebraicGeometry.Correspondence.Graph
public import ReasLib.AlgebraicGeometry.Correspondence.Transpose.Graph
public import ReasLib.AlgebraicGeometry.ChowMotive.Duality
public import ReasLib.AlgebraicGeometry.ChowMotive.Tate
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
public import ReasLib.CategoryTheory.Idempotents.Karoubi.Monoidal
public import Mathlib.CategoryTheory.Idempotents.Biproducts

@[expose] public section

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Correspondence
open scoped CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace ChowMotive.ProjectiveLine

variable {k : Type u} [Field k]

/-- The degree-zero graded projector induced by `pointTimes x` is idempotent. -/
theorem pointProjector_idem
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    let X := Correspondence.GradedCategory.ofScheme
      (ProjectiveSpace.schemeOver k 1) 0
    let p : X ⟶ X := Correspondence.GradedCategory.homOfDegreeZero rfl
      (Correspondence.ProjectiveLine.pointTimes x)
    p ≫ p = p := sorry

/-- The projective-line Chow motive cut out by `c₀ = pointTimes x`. -/
noncomputable def pointProjectorMotive
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) where
  X := Correspondence.GradedCategory.ofScheme (ProjectiveSpace.schemeOver k 1) 0
  p := Correspondence.GradedCategory.homOfDegreeZero rfl
    (Correspondence.ProjectiveLine.pointTimes x)
  idem := pointProjector_idem x

/-- The underlying graded object of `pointProjectorMotive x` is `ℙ¹_k` in degree zero. -/
theorem pointProjectorMotive_X
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    (pointProjectorMotive x).X = Correspondence.GradedCategory.ofScheme
      (ProjectiveSpace.schemeOver k 1) 0 := sorry

/-- The projector of `pointProjectorMotive x` is the graded form of `pointTimes x`. -/
theorem pointProjectorMotive_p
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    (pointProjectorMotive x).p = Correspondence.GradedCategory.homOfDegreeZero rfl
      (Correspondence.ProjectiveLine.pointTimes x) := sorry

/-- The graph of `x` satisfies the Karoubi compatibility for the map to the tensor unit. -/
theorem pointProjectorHomUnit_comm
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    let f : (pointProjectorMotive x).X ⟶
        (𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))).X :=
      Correspondence.GradedCategory.homOfDegreeZero rfl
        (Correspondence.rationalGraph x)
    (pointProjectorMotive x).p ≫ f ≫
      (𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))).p = f := sorry

/-- The graph of `x` as a morphism from the `c₀` summand to the tensor unit. -/
noncomputable def pointProjectorHomUnit
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    pointProjectorMotive x ⟶
      𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) where
  f := Correspondence.GradedCategory.homOfDegreeZero rfl
    (Correspondence.rationalGraph x)
  comm := pointProjectorHomUnit_comm x

/-- The graph of the structure map satisfies the Karoubi compatibility for the inverse map. -/
theorem unitHomPointProjector_comm
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    let f : (𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))).X ⟶
        (pointProjectorMotive x).X :=
      Correspondence.GradedCategory.homOfDegreeZero rfl
        (Correspondence.rationalGraph
          (terminal.from (ProjectiveSpace.schemeOver k 1)))
    (𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))).p ≫ f ≫
      (pointProjectorMotive x).p = f := sorry

/-- The graph of the structure map as a morphism from the tensor unit to the `c₀` summand. -/
noncomputable def unitHomPointProjector
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) ⟶
      pointProjectorMotive x where
  f := Correspondence.GradedCategory.homOfDegreeZero rfl
    (Correspondence.rationalGraph
      (terminal.from (ProjectiveSpace.schemeOver k 1)))
  comm := unitHomPointProjector_comm x

/-- The graph maps compose to the identity of the `c₀` summand. -/
theorem pointProjectorIsoUnit_hom_inv_id
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    pointProjectorHomUnit x ≫ unitHomPointProjector x = 𝟙 _ := sorry

/-- The graph maps compose to the identity of the tensor unit. -/
theorem pointProjectorIsoUnit_inv_hom_id
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    unitHomPointProjector x ≫ pointProjectorHomUnit x = 𝟙 _ := sorry

/-- The projective-line motive cut out by `c₀` is isomorphic to the tensor unit. -/
noncomputable def pointProjectorIsoUnit
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    pointProjectorMotive x ≅
      𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) where
  hom := pointProjectorHomUnit x
  inv := unitHomPointProjector x
  hom_inv_id := pointProjectorIsoUnit_hom_inv_id x
  inv_hom_id := pointProjectorIsoUnit_inv_hom_id x

/-- The underlying hom of `pointProjectorIsoUnit x` is the graph of `x`. -/
theorem pointProjectorIsoUnit_hom_f
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    (pointProjectorIsoUnit x).hom.f =
      (Correspondence.GradedCategory.homOfDegreeZero rfl
        (Correspondence.rationalGraph x : Correspondence.Rational
          (ProjectiveSpace.schemeOver k 1) (SchemeOverField.point k) 0) :
        Correspondence.GradedCategory.ofScheme (ProjectiveSpace.schemeOver k 1) 0 ⟶
          Correspondence.GradedCategory.tensorUnit k) := sorry

/-- The underlying inverse of `pointProjectorIsoUnit x` is the graph of the structure map. -/
theorem pointProjectorIsoUnit_inv_f
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    (pointProjectorIsoUnit x).inv.f =
      (Correspondence.GradedCategory.homOfDegreeZero rfl
        (Correspondence.rationalGraph
          (terminal.from (ProjectiveSpace.schemeOver k 1)) :
            Correspondence.Rational (SchemeOverField.point k)
              (ProjectiveSpace.schemeOver k 1) 0) :
        Correspondence.GradedCategory.tensorUnit k ⟶
          Correspondence.GradedCategory.ofScheme (ProjectiveSpace.schemeOver k 1) 0) := sorry

/-- The degree-zero graded projector induced by `timesPoint x` is idempotent. -/
theorem tateProjector_idem
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    let X := Correspondence.GradedCategory.ofScheme
      (ProjectiveSpace.schemeOver k 1) 0
    let p : X ⟶ X := Correspondence.GradedCategory.homOfDegreeZero rfl
      (Correspondence.ProjectiveLine.timesPoint x)
    p ≫ p = p := sorry

/-- The projective-line Chow motive cut out by `c₂ = timesPoint x`. -/
noncomputable def tateProjectorMotive
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) where
  X := Correspondence.GradedCategory.ofScheme (ProjectiveSpace.schemeOver k 1) 0
  p := Correspondence.GradedCategory.homOfDegreeZero rfl
    (Correspondence.ProjectiveLine.timesPoint x)
  idem := tateProjector_idem x

/-- The underlying graded object of `tateProjectorMotive x` is `ℙ¹_k` in degree zero. -/
theorem tateProjectorMotive_X
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    (tateProjectorMotive x).X = Correspondence.GradedCategory.ofScheme
      (ProjectiveSpace.schemeOver k 1) 0 := sorry

/-- The projector of `tateProjectorMotive x` is the graded form of `timesPoint x`. -/
theorem tateProjectorMotive_p
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    (tateProjectorMotive x).p = Correspondence.GradedCategory.homOfDegreeZero rfl
      (Correspondence.ProjectiveLine.timesPoint x) := sorry

/-- The transposed graph of the structure map satisfies the Karoubi compatibility
for the map to the Tate twist. -/
theorem tateProjectorHomTwist_comm
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    let f : (tateProjectorMotive x).X ⟶
        (ChowMotive.tateTwist (SchemeOverField.point k) (-1)).X :=
      Correspondence.transposedGraph (SchemeOverField.point k)
        (ProjectiveSpace.schemeOver k 1) 0 1 ChowMotive.point_dimension
        (Correspondence.ProjectiveLine.lineDimension k)
        (terminal.from (ProjectiveSpace.schemeOver k 1))
    (tateProjectorMotive x).p ≫ f ≫
      (ChowMotive.tateTwist (SchemeOverField.point k) (-1)).p = f := sorry

/-- The transposed graph of the structure map as a morphism from the `c₂` summand
to the Tate twist. -/
noncomputable def tateProjectorHomTwist
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    tateProjectorMotive x ⟶ ChowMotive.tateTwist (SchemeOverField.point k) (-1) where
  f := Correspondence.transposedGraph (SchemeOverField.point k)
    (ProjectiveSpace.schemeOver k 1) 0 1 ChowMotive.point_dimension
    (Correspondence.ProjectiveLine.lineDimension k)
    (terminal.from (ProjectiveSpace.schemeOver k 1))
  comm := tateProjectorHomTwist_comm x

/-- The transposed graph of `x` satisfies the Karoubi compatibility for the inverse
map from the Tate twist. -/
theorem twistHomTateProjector_comm
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    let f : (ChowMotive.tateTwist (SchemeOverField.point k) (-1)).X ⟶
        (tateProjectorMotive x).X :=
      Correspondence.transposedGraph (ProjectiveSpace.schemeOver k 1)
        (SchemeOverField.point k) 1 0
        (Correspondence.ProjectiveLine.lineDimension k) ChowMotive.point_dimension x
    (ChowMotive.tateTwist (SchemeOverField.point k) (-1)).p ≫ f ≫
      (tateProjectorMotive x).p = f := sorry

/-- The transposed graph of `x` as a morphism from the Tate twist to the `c₂` summand. -/
noncomputable def twistHomTateProjector
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    ChowMotive.tateTwist (SchemeOverField.point k) (-1) ⟶ tateProjectorMotive x where
  f := Correspondence.transposedGraph (ProjectiveSpace.schemeOver k 1)
    (SchemeOverField.point k) 1 0
    (Correspondence.ProjectiveLine.lineDimension k) ChowMotive.point_dimension x
  comm := twistHomTateProjector_comm x

/-- The transposed-graph maps compose to the identity of the `c₂` summand. -/
theorem tateProjectorIsoTwist_hom_inv_id
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    tateProjectorHomTwist x ≫ twistHomTateProjector x = 𝟙 _ := sorry

/-- The transposed-graph maps compose to the identity of the Tate twist. -/
theorem tateProjectorIsoTwist_inv_hom_id
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    twistHomTateProjector x ≫ tateProjectorHomTwist x = 𝟙 _ := sorry

/-- The projective-line motive cut out by `c₂` is isomorphic to the Tate twist of the
tensor unit in degree `-1`. -/
noncomputable def tateProjectorIsoTwist
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    tateProjectorMotive x ≅ ChowMotive.tateTwist (SchemeOverField.point k) (-1) where
  hom := tateProjectorHomTwist x
  inv := twistHomTateProjector x
  hom_inv_id := tateProjectorIsoTwist_hom_inv_id x
  inv_hom_id := tateProjectorIsoTwist_inv_hom_id x

/-- The underlying hom of `tateProjectorIsoTwist x` is the transposed graph of the
structure map in degree `-1`. -/
theorem tateProjectorIsoTwist_hom_f
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    (tateProjectorIsoTwist x).hom.f =
      Correspondence.transposedGraph (SchemeOverField.point k)
        (ProjectiveSpace.schemeOver k 1) 0 1 ChowMotive.point_dimension
        (Correspondence.ProjectiveLine.lineDimension k)
        (terminal.from (ProjectiveSpace.schemeOver k 1)) := sorry

/-- The underlying inverse of `tateProjectorIsoTwist x` is the transposed graph of `x`
in degree `1`. -/
theorem tateProjectorIsoTwist_inv_f
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    (tateProjectorIsoTwist x).inv.f =
      Correspondence.transposedGraph (ProjectiveSpace.schemeOver k 1)
        (SchemeOverField.point k) 1 0
        (Correspondence.ProjectiveLine.lineDimension k) ChowMotive.point_dimension x := sorry


/-- The standard section `[1 : 0]` is compatible with the structure maps to `Spec k`. -/
theorem zeroSectionOver_fac (k : Type u) [Field k] :
    (SchemeOverField.point k).hom ≫ AlgebraicGeometry.ProjectiveLine.zeroSection k ≫
      (ProjectiveSpace.schemeOver k 1).hom = (SchemeOverField.point k).hom := sorry

/-- The standard rational point `[1 : 0]` of the projective line over `k`. -/
noncomputable def zeroSectionOver (k : Type u) [Field k] :
    SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1 :=
  Over.homMk
    ((SchemeOverField.point k).hom ≫ AlgebraicGeometry.ProjectiveLine.zeroSection k :
      (SchemeOverField.point k).left ⟶ (ProjectiveSpace.schemeOver k 1).left)
    (zeroSectionOver_fac k)

/-- The underlying scheme morphism of `zeroSectionOver k` is induced by the standard
`[1 : 0]` section. -/
theorem zeroSectionOver_left (k : Type u) [Field k] :
    (zeroSectionOver k).left =
      ((SchemeOverField.point k).hom ≫ AlgebraicGeometry.ProjectiveLine.zeroSection k :
        (SchemeOverField.point k).left ⟶ (ProjectiveSpace.schemeOver k 1).left) := sorry

/-- The `c₂` correspondence satisfies the Karoubi compatibility from the complement
of the `c₀` projector to the `c₂` projector. -/
theorem complementHomTate_comm
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    let f : (pointProjectorMotive x).complement.X ⟶ (tateProjectorMotive x).X :=
      Correspondence.GradedCategory.homOfDegreeZero rfl
        (Correspondence.ProjectiveLine.timesPoint x)
    (pointProjectorMotive x).complement.p ≫ f ≫ (tateProjectorMotive x).p = f := sorry

/-- The `c₂` correspondence as a morphism from the complement of the `c₀` projector
to the `c₂` projector. -/
noncomputable def complementHomTate
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    (pointProjectorMotive x).complement ⟶ tateProjectorMotive x where
  f := Correspondence.GradedCategory.homOfDegreeZero rfl
    (Correspondence.ProjectiveLine.timesPoint x)
  comm := complementHomTate_comm x

/-- The `c₂` correspondence satisfies the Karoubi compatibility from the `c₂`
projector to the complement of the `c₀` projector. -/
theorem tateHomComplement_comm
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    let f : (tateProjectorMotive x).X ⟶ (pointProjectorMotive x).complement.X :=
      Correspondence.GradedCategory.homOfDegreeZero rfl
        (Correspondence.ProjectiveLine.timesPoint x)
    (tateProjectorMotive x).p ≫ f ≫ (pointProjectorMotive x).complement.p = f := sorry

/-- The `c₂` correspondence as a morphism from the `c₂` projector to the complement
of the `c₀` projector. -/
noncomputable def tateHomComplement
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    tateProjectorMotive x ⟶ (pointProjectorMotive x).complement where
  f := Correspondence.GradedCategory.homOfDegreeZero rfl
    (Correspondence.ProjectiveLine.timesPoint x)
  comm := tateHomComplement_comm x

/-- The two `c₂` morphisms compose to the identity of the complementary projector. -/
theorem complementHomTate_tateHomComplement
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    complementHomTate x ≫ tateHomComplement x = 𝟙 _ := sorry

/-- The two `c₂` morphisms compose to the identity of the `c₂` projector. -/
theorem tateHomComplement_complementHomTate
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    tateHomComplement x ≫ complementHomTate x = 𝟙 _ := sorry

/-- The complement of the `c₀` projector is canonically the `c₂` projector motive. -/
noncomputable def complementIsoTate
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    (pointProjectorMotive x).complement ≅ tateProjectorMotive x where
  hom := complementHomTate x
  inv := tateHomComplement x
  hom_inv_id := complementHomTate_tateHomComplement x
  inv_hom_id := tateHomComplement_complementHomTate x

/-- The underlying hom of `complementIsoTate x` is the graded `c₂` correspondence. -/
theorem complementIsoTate_hom_f
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    (complementIsoTate x).hom.f = Correspondence.GradedCategory.homOfDegreeZero rfl
      (Correspondence.ProjectiveLine.timesPoint x) := sorry

/-- The underlying inverse of `complementIsoTate x` is the graded `c₂` correspondence. -/
theorem complementIsoTate_inv_f
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    (complementIsoTate x).inv.f = Correspondence.GradedCategory.homOfDegreeZero rfl
      (Correspondence.ProjectiveLine.timesPoint x) := sorry

/-- The tensor unit and its Tate twist by `-1` have a canonical binary biproduct,
transported from the two complementary projectors at `[1 : 0]`. -/
noncomputable instance instHasBinaryBiproductUnitTate (k : Type u) [Field k] :
    HasBinaryBiproduct
      (𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)))
      (ChowMotive.tateTwist (SchemeOverField.point k) (-1)) :=
  hasBinaryBiproduct_of_iso
    (pointProjectorIsoUnit (zeroSectionOver k))
    (complementIsoTate (zeroSectionOver k) ≪≫
      tateProjectorIsoTwist (zeroSectionOver k))

/-- The projective-line motive decomposition determined by a rational point `x`. -/
noncomputable def decompositionAt
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    ChowMotive.h (ProjectiveSpace.schemeOver k 1) ≅
      𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) ⊞
        ChowMotive.tateTwist (SchemeOverField.point k) (-1) :=
  (Karoubi.decomposition (pointProjectorMotive x)).symm ≪≫
    biprod.mapIso (pointProjectorIsoUnit x)
      (complementIsoTate x ≪≫ tateProjectorIsoTwist x)

/-- The hom of `decompositionAt x` is the projector decomposition followed by the
isomorphisms identifying its two summands. -/
theorem decompositionAt_hom
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    (decompositionAt x).hom =
      (Karoubi.decomposition (pointProjectorMotive x)).inv ≫
        (biprod.mapIso (pointProjectorIsoUnit x)
          (complementIsoTate x ≪≫ tateProjectorIsoTwist x)).hom := sorry

/-- The inverse of `decompositionAt x` first identifies the two summands and then
reassembles the complementary projectors. -/
theorem decompositionAt_inv
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    (decompositionAt x).inv =
      (biprod.mapIso (pointProjectorIsoUnit x)
        (complementIsoTate x ≪≫ tateProjectorIsoTwist x)).inv ≫
        (Karoubi.decomposition (pointProjectorMotive x)).hom := sorry

/-- The canonical decomposition of the projective-line Chow motive into the tensor
unit and its Tate twist by `-1`. -/
noncomputable def decomposition {k : Type u} [Field k] :
    ChowMotive.h (ProjectiveSpace.schemeOver k 1) ≅
      𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) ⊞
        ChowMotive.tateTwist (SchemeOverField.point k) (-1) :=
  decompositionAt (zeroSectionOver k)

/-- The canonical decomposition is the rational-point decomposition at `[1 : 0]`. -/
theorem decomposition_eq_decompositionAt {k : Type u} [Field k] :
    decomposition = decompositionAt (zeroSectionOver k) := sorry


/-- The Lefschetz projector motive has the point Tate twist of index `1` as an explicit
right tensor inverse. -/
noncomputable def lefschetzTensorTateIso
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    tateProjectorMotive x ⊗ ChowMotive.tateTwist (SchemeOverField.point k) 1 ≅
      𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :=
  MonoidalCategory.tensorIso (tateProjectorIsoTwist x) (Iso.refl _) ≪≫
    ChowMotive.Tate.rightInverseIso k (-1)

/-- The Lefschetz-right-inverse comparison is obtained by tensoring the projector-to-twist
isomorphism with the identity of the point Tate twist of index `1`. -/
theorem lefschetzTensorTateIso_def
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    lefschetzTensorTateIso x =
      MonoidalCategory.tensorIso (tateProjectorIsoTwist x) (Iso.refl _) ≪≫
        ChowMotive.Tate.rightInverseIso k (-1) := sorry

/-- The point Tate twist of index `1` is also an explicit left tensor inverse of the
Lefschetz projector motive. -/
noncomputable def tateTensorLefschetzIso
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    ChowMotive.tateTwist (SchemeOverField.point k) 1 ⊗ tateProjectorMotive x ≅
      𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :=
  MonoidalCategory.tensorIso (Iso.refl _) (tateProjectorIsoTwist x) ≪≫
    ChowMotive.Tate.leftInverseIso k (-1)

/-- The Tate-left-inverse comparison is obtained by tensoring the identity of the point
Tate twist of index `1` with the projector-to-twist isomorphism. -/
theorem tateTensorLefschetzIso_def
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    tateTensorLefschetzIso x =
      MonoidalCategory.tensorIso (Iso.refl _) (tateProjectorIsoTwist x) ≪≫
        ChowMotive.Tate.leftInverseIso k (-1) := sorry

/-- The Lefschetz projector motive is tensor-invertible. -/
instance instIsInvertibleObjectTateProjectorMotive
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) :
    MonoidalCategory.isInvertibleObject (tateProjectorMotive x) := sorry

end ChowMotive.ProjectiveLine
