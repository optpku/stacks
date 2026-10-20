/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Product
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Separation

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Solution
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.ComplementInclusion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Slice
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction.Construction

/-!
# Diagonal equalizers of contraction triples

Algebraic and formal equalizers of compatible contraction triples define a
contraction situation over the test scheme and characterize their agreement.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- The equalizer of interpolating maps `x'_i : V'_i ⟶ X'` and of completed maps
`hatx_i : V_{/Z_i} ⟶ W`, together with the comparison morphism from the
completion of `E'` along the inverse image of `Z = Z_1 ∩ Z_2`. -/
structure DiagonalEqualizer {σ : ContractionSituation S} {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left]
    (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) where
  /-- The fibre product `V' = V'_1 ×_V V'_2`. -/
  pullbackSpace : AlgebraicSpace S
  /-- The equalizer `E'` of `V' ⟶ V'_i ⟶ X'`. -/
  space : AlgebraicSpace S
  /-- The structure morphism `E' ⟶ V`. -/
  toV : space ⟶ ofOver V
  /-- The equalized interpolating morphism `E' ⟶ X'`. -/
  spaceHom : space ⟶ σ.X'
  /-- The closed subset `Z = Z_1 ∩ Z_2`. -/
  closed : Closeds (Points (ofOver V))
  /-- The equalizer `E_W` of `V_{/Z} ⟶ V_{/Z_i} ⟶ W`. -/
  formal : (Over S)ᵒᵖ ⥤ Type u
  /-- The inclusion `E_W ⟶ V_{/Z}`. -/
  toFormal : formal ⟶ completionAlong (ofOver V) closed
  /-- The comparison `E'_{/Z} ⟶ E_W` through which `E'_{/Z} ⟶ V_{/Z}` factors. -/
  factor :
    completionAlong space (closed.preimage (Points.continuous_map toV)) ⟶ formal

namespace DiagonalEqualizer

variable {σ : ContractionSituation S} {V : Over S}
  [AlgebraicGeometry.IsLocallyNoetherian V.left]

/-- The fibre product `V'_1 ×_V V'_2` of interpolating dilatations. -/
def interpPullback (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) : AlgebraicSpace S :=
  pullback w1.toV w2.toV

/-- The interpolating map `V' ⟶ V'_1 ⟶ X'`. -/
def leftHom (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    interpPullback ξ1 ξ2 w1 w2 ⟶ σ.X' :=
  pullback.fst w1.toV w2.toV ≫ w1.x'

/-- The interpolating map `V' ⟶ V'_2 ⟶ X'`. -/
def rightHom (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    interpPullback ξ1 ξ2 w1 w2 ⟶ σ.X' :=
  pullback.snd w1.toV w2.toV ≫ w2.x'

/-- The pair morphism `(x'_1, x'_2) : V' ⟶ X' ⨯ X'`. -/
def pairHom (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    interpPullback ξ1 ξ2 w1 w2 ⟶ σ.X' ⨯ σ.X' :=
  prod.lift (leftHom ξ1 ξ2 w1 w2) (rightHom ξ1 ξ2 w1 w2)

/-- The diagonal morphism `X' ⟶ X' ⨯ X'`. -/
def diagHom (σ : ContractionSituation S) : σ.X' ⟶ σ.X' ⨯ σ.X' :=
  prod.lift (𝟙 σ.X') (𝟙 σ.X')

/-- The equalizer `E'` of the interpolating maps into `X'`. -/
def interpSpace (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) : AlgebraicSpace S :=
  pullback (pairHom ξ1 ξ2 w1 w2) (diagHom σ)

/-- The structure morphism `E' ⟶ V`. -/
def interpToV (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    interpSpace ξ1 ξ2 w1 w2 ⟶ ofOver V :=
  pullback.fst (pairHom ξ1 ξ2 w1 w2) (diagHom σ) ≫
    pullback.fst w1.toV w2.toV ≫ w1.toV

/-- The closed subset `Z = Z_1 ∩ Z_2`. -/
def interClosed (ξ1 ξ2 : Triple σ V) : Closeds (Points (ofOver V)) :=
  ξ1.Z ⊓ ξ2.Z

/-- The identity on `V` sends `Z` into `Z_1`. -/
theorem interClosed_subset_left (ξ1 ξ2 : Triple σ V) :
    Points.map (𝟙 (ofOver V)) ''
        ((interClosed ξ1 ξ2 : Closeds (Points (ofOver V))) : Set _) ⊆
      (ξ1.Z : Set (Points (ofOver V))) :=
  sorry

/-- The identity on `V` sends `Z` into `Z_2`. -/
theorem interClosed_subset_right (ξ1 ξ2 : Triple σ V) :
    Points.map (𝟙 (ofOver V)) ''
        ((interClosed ξ1 ξ2 : Closeds (Points (ofOver V))) : Set _) ⊆
      (ξ2.Z : Set (Points (ofOver V))) :=
  sorry

/-- The completed map `V_{/Z} ⟶ V_{/Z_1} ⟶ W`. -/
def leftHat (ξ1 ξ2 : Triple σ V) :
    completionAlong (ofOver V) (interClosed ξ1 ξ2) ⟶ σ.W :=
  completionAlong.mapOfLe (𝟙 (ofOver V)) (interClosed ξ1 ξ2) ξ1.Z
      (interClosed_subset_left ξ1 ξ2) ≫
    ξ1.hatx

/-- The completed map `V_{/Z} ⟶ V_{/Z_2} ⟶ W`. -/
def rightHat (ξ1 ξ2 : Triple σ V) :
    completionAlong (ofOver V) (interClosed ξ1 ξ2) ⟶ σ.W :=
  completionAlong.mapOfLe (𝟙 (ofOver V)) (interClosed ξ1 ξ2) ξ2.Z
      (interClosed_subset_right ξ1 ξ2) ≫
    ξ2.hatx

/-- The equalizer `E_W` of the completed maps into `W`. -/
def interpFormal (ξ1 ξ2 : Triple σ V) : (Over S)ᵒᵖ ⥤ Type u :=
  equalizer (leftHat ξ1 ξ2) (rightHat ξ1 ξ2)

/-- The inclusion `E_W ⟶ V_{/Z}`. -/
def interpToFormal (ξ1 ξ2 : Triple σ V) :
    interpFormal ξ1 ξ2 ⟶ completionAlong (ofOver V) (interClosed ξ1 ξ2) :=
  equalizer.ι (leftHat ξ1 ξ2) (rightHat ξ1 ξ2)

/-- The inverse image of `Z` along `E' ⟶ V`. -/
def spaceClosed (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    Closeds (Points (interpSpace ξ1 ξ2 w1 w2)) :=
  (interClosed ξ1 ξ2).preimage (Points.continuous_map (interpToV ξ1 ξ2 w1 w2))

/-- Completing `E' ⟶ V` along `Z` equalizes the two completed maps into `W`. -/
theorem map_comp_equalizes (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    completionAlong.map (interpToV ξ1 ξ2 w1 w2) (interClosed ξ1 ξ2) ≫
        leftHat ξ1 ξ2 =
      completionAlong.map (interpToV ξ1 ξ2 w1 w2) (interClosed ξ1 ξ2) ≫
        rightHat ξ1 ξ2 :=
  sorry

/-- The comparison `E'_{/Z} ⟶ E_W`. -/
def interpFactor (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    completionAlong (interpSpace ξ1 ξ2 w1 w2) (spaceClosed ξ1 ξ2 w1 w2) ⟶
      interpFormal ξ1 ξ2 :=
  equalizer.lift (completionAlong.map (interpToV ξ1 ξ2 w1 w2) (interClosed ξ1 ξ2))
    (map_comp_equalizes ξ1 ξ2 w1 w2)

/-- The diagonal equalizer formed by the witness fiber product, the algebraic
and formal equalizers, and their canonical comparison. -/
def of (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    DiagonalEqualizer ξ1 ξ2 w1 w2 where
  pullbackSpace := interpPullback ξ1 ξ2 w1 w2
  space := interpSpace ξ1 ξ2 w1 w2
  toV := interpToV ξ1 ξ2 w1 w2
  spaceHom :=
    pullback.fst (pairHom ξ1 ξ2 w1 w2) (diagHom σ) ≫ leftHom ξ1 ξ2 w1 w2
  closed := interClosed ξ1 ξ2
  formal := interpFormal ξ1 ξ2
  toFormal := interpToFormal ξ1 ξ2
  factor := interpFactor ξ1 ξ2 w1 w2

variable {ξ1 ξ2 : Triple σ V}
  {w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx}
  {w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx}

/-- The stored fibre product is `V'_1 ×_V V'_2`. -/
theorem pullbackSpace_eq :
    (of ξ1 ξ2 w1 w2).pullbackSpace = pullback w1.toV w2.toV :=
  rfl

/-- The stored space is the diagonal pullback of the interpolating pair. -/
theorem space_eq :
    (of ξ1 ξ2 w1 w2).space = pullback (pairHom ξ1 ξ2 w1 w2) (diagHom σ) :=
  rfl

/-- The stored closed subset is the intersection `Z_1 ∩ Z_2`. -/
theorem closed_eq : (of ξ1 ξ2 w1 w2).closed = ξ1.Z ⊓ ξ2.Z :=
  rfl

/-- The stored formal equalizer is the functor equalizer of `leftHat` and
`rightHat`. -/
theorem formal_eq :
    (of ξ1 ξ2 w1 w2).formal = equalizer (leftHat ξ1 ξ2) (rightHat ξ1 ξ2) :=
  rfl

/-- Postcomposing `factor` with `toFormal` recovers the completion of `toV`. -/
theorem factor_comp_ι :
    (of ξ1 ξ2 w1 w2).factor ≫ (of ξ1 ξ2 w1 w2).toFormal =
      completionAlong.map (interpToV ξ1 ξ2 w1 w2) (interClosed ξ1 ξ2) :=
  sorry

/-- Completing `spaceHom` along `T'` sends the inverse image of `Z` into `T'`. -/
theorem spaceHom_mapsClosed (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    Points.map (of ξ1 ξ2 w1 w2).spaceHom ''
        (((of ξ1 ξ2 w1 w2).closed.preimage
            (Points.continuous_map (of ξ1 ξ2 w1 w2).toV) : Closeds _) : Set _) ⊆
      (σ.T' : Set (Points σ.X')) :=
  sorry

/-- The completed interpolating map `E'_{/Z} ⟶ X'_{/T'}`. -/
def completionSpace (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    completionAlong (of ξ1 ξ2 w1 w2).space
      ((of ξ1 ξ2 w1 w2).closed.preimage
        (Points.continuous_map (of ξ1 ξ2 w1 w2).toV)) ⟶
      σ.completion :=
  completionAlong.mapOfLe (of ξ1 ξ2 w1 w2).spaceHom
    ((of ξ1 ξ2 w1 w2).closed.preimage
      (Points.continuous_map (of ξ1 ξ2 w1 w2).toV))
    σ.T' (spaceHom_mapsClosed ξ1 ξ2 w1 w2)

/-- The structure morphism of `E_W` over `V`. -/
def toOver (D : DiagonalEqualizer ξ1 ξ2 w1 w2) : D.formal ⟶ (ofOver V).functorOfPoints :=
  D.toFormal ≫ completionAlong.ι (ofOver V) D.closed

/-- The open fibre product `E' ×_V (V \ Z)`. -/
def openPullback (D : DiagonalEqualizer ξ1 ξ2 w1 w2) : AlgebraicSpace S :=
  pullback D.toV (AlgebraicSpace.openComplementι (ofOver V) D.closed)

/-- The projection `E' ×_V (V \ Z) ⟶ V \ Z`. -/
def openPullbackSnd (D : DiagonalEqualizer ξ1 ξ2 w1 w2) : openPullback D ⟶
    openComplementAlong (ofOver V) D.closed :=
  pullback.snd D.toV (AlgebraicSpace.openComplementι (ofOver V) D.closed)

/-- `E' ⟶ V` is separated. -/
theorem instSeparated_toV (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    Separated (interpToV ξ1 ξ2 w1 w2) :=
  sorry

/-- `E' ⟶ V` is locally of finite type. -/
theorem instLocallyOfFiniteType_toV (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    LocallyOfFiniteType (interpToV ξ1 ξ2 w1 w2) :=
  sorry

/-- `E'` is locally Noetherian. -/
theorem instIsLocallyNoetherian_space (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    IsLocallyNoetherian (interpSpace ξ1 ξ2 w1 w2) :=
  sorry

/-- `E_W` is a formal algebraic space. -/
theorem instIsFormal_formal (ξ1 ξ2 : Triple σ V) :
    FormalAlgebraicSpace.IsFormalAlgebraicSpace (interpFormal ξ1 ξ2) :=
  sorry

/-- `E_W` is locally Noetherian. -/
theorem instIsLocallyNoetherian_formal (ξ1 ξ2 : Triple σ V) :
    @FormalAlgebraicSpace.IsLocallyNoetherian _ (interpFormal ξ1 ξ2)
      (instIsFormal_formal ξ1 ξ2) :=
  sorry

/-- The structure morphism of the canonical formal equalizer over `V`. -/
def interpToOver (ξ1 ξ2 : Triple σ V) :
    interpFormal ξ1 ξ2 ⟶ (ofOver V).functorOfPoints :=
  interpToFormal ξ1 ξ2 ≫ completionAlong.ι (ofOver V) (interClosed ξ1 ξ2)

/-- `E_W` is separated over `V`. -/
theorem instSeparated_formal (ξ1 ξ2 : Triple σ V) :
    FormalAlgebraicSpace.Separated (interpToOver ξ1 ξ2) :=
  sorry

/-- The comparison `E'_{/Z} ⟶ E_W` is locally of finite type. -/
theorem instLocallyOfFiniteType_factor (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    FormalAlgebraicSpace.LocallyOfFiniteType (interpFactor ξ1 ξ2 w1 w2) :=
  sorry

/-- The comparison factors the completed structure map, and its square with the original formal modification is cartesian. -/
theorem _root_.AlgebraicGeometry.AlgebraicSpace.ContractionSituation.isPullback_factor (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    (DiagonalEqualizer.of ξ1 ξ2 w1 w2).factor ≫
          (DiagonalEqualizer.of ξ1 ξ2 w1 w2).toFormal =
        completionAlong.map (DiagonalEqualizer.of ξ1 ξ2 w1 w2).toV
          (DiagonalEqualizer.of ξ1 ξ2 w1 w2).closed ∧
      IsPullback
        (DiagonalEqualizer.completionSpace ξ1 ξ2 w1 w2)
        (DiagonalEqualizer.of ξ1 ξ2 w1 w2).factor σ.g
        ((DiagonalEqualizer.of ξ1 ξ2 w1 w2).toFormal ≫
          DiagonalEqualizer.leftHat ξ1 ξ2) :=
  sorry

/-- The comparison `E'_{/Z} ⟶ E_W` is a formal modification. -/
theorem instFormalModification_factor (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    @FormalAlgebraicSpace.FormalModification S
      (completionAlong (interpSpace ξ1 ξ2 w1 w2) (spaceClosed ξ1 ξ2 w1 w2)) (interpFormal ξ1 ξ2)
      (interpFactor ξ1 ξ2 w1 w2)
      (instIsFormalAlgebraicSpace_completionAlong (interpSpace ξ1 ξ2 w1 w2) (spaceClosed ξ1 ξ2 w1 w2))
      (instIsFormal_formal ξ1 ξ2)
      (@instIsLocallyNoetherian_completionAlong S (interpSpace ξ1 ξ2 w1 w2)
        (instIsLocallyNoetherian_space ξ1 ξ2 w1 w2) (spaceClosed ξ1 ξ2 w1 w2))
      (instIsLocallyNoetherian_formal ξ1 ξ2) (instLocallyOfFiniteType_factor ξ1 ξ2 w1 w2) :=
  sorry

/-- The restriction of `ξ1.u'` to `V \ (Z_1 ∪ Z_2)`. -/
def leftOpen (ξ1 ξ2 : Triple σ V) :
    openComplementAlong (ofOver V) (ξ1.Z ⊔ ξ2.Z) ⟶ σ.openComplement :=
  openComplementAlong.mapOfLe le_sup_left ≫ ξ1.u'

/-- The restriction of `ξ2.u'` to `V \ (Z_1 ∪ Z_2)`. -/
def rightOpen (ξ1 ξ2 : Triple σ V) :
    openComplementAlong (ofOver V) (ξ1.Z ⊔ ξ2.Z) ⟶ σ.openComplement :=
  openComplementAlong.mapOfLe le_sup_right ≫ ξ2.u'

/-- The image of the interpolating equalizer meets the union of the two closed subsets only in their intersection. -/
theorem _root_.AlgebraicGeometry.AlgebraicSpace.ContractionSituation.image_inter_subset (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    Set.range (Points.map (DiagonalEqualizer.of ξ1 ξ2 w1 w2).toV) ∩
        (ξ1.Z ∪ ξ2.Z) ⊆
      (ξ1.Z ⊓ ξ2.Z : Set _) :=
  sorry

/-- The underlying `V`-section of `E' ×_V (V \ Z)` lands in
`V \ (Z_1 ∪ Z_2)`. -/
theorem openRestrict_spec (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx)
    {U : (Over S)ᵒᵖ}
    (x : (openPullback (of ξ1 ξ2 w1 w2)).functorOfPoints.obj U) :
    Set.range
        (Points.map (X := ofOver U.unop) (Y := ofOver V)
          (yonedaEquiv.symm
            ((openPullbackSnd (of ξ1 ξ2 w1 w2)).app U x).1 :
              ofOver U.unop ⟶ ofOver V)) ⊆
      (ξ1.Z ⊔ ξ2.Z : Set (Points (ofOver V)))ᶜ :=
  sorry

/-- The induced morphism `E' ×_V (V \ Z) ⟶ V \ (Z_1 ∪ Z_2)`. -/
def openRestrict (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    openPullback (of ξ1 ξ2 w1 w2) ⟶
      openComplementAlong (ofOver V) (ξ1.Z ⊔ ξ2.Z) where
  app U := ofHom fun x ↦
    ⟨(openPullbackSnd (of ξ1 ξ2 w1 w2)).app U x |>.1,
      openRestrict_spec ξ1 ξ2 w1 w2 x⟩
  naturality := sorry

/-- Postcomposing `openRestrict` with the inclusion of
`V \ (Z_1 ∪ Z_2)` into `V \ Z` recovers the projection to `V \ Z`. -/
theorem openRestrict_comp_mapOfLe (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    openRestrict ξ1 ξ2 w1 w2 ≫
        openComplementAlong.mapOfLe
          (inf_le_sup : ξ1.Z ⊓ ξ2.Z ≤ ξ1.Z ⊔ ξ2.Z) =
      openPullbackSnd (of ξ1 ξ2 w1 w2) :=
  sorry

/-- The algebraic space over `V` whose `T`-points are maps into `E'` over `V`. -/
def sliceSpace (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    AlgebraicSpace V.left :=
  AlgebraicSpace.sliceSpace (of ξ1 ξ2 w1 w2).space (of ξ1 ξ2 w1 w2).toV

/-- `E'` over `V` is locally of finite type. -/
theorem instLocallyOfFiniteType_sliceSpace (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    LocallyOfFiniteType (toBase (sliceSpace ξ1 ξ2 w1 w2)) :=
  sorry

/-- `E'` over `V` is locally Noetherian. -/
theorem instIsLocallyNoetherian_sliceSpace (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    IsLocallyNoetherian (sliceSpace ξ1 ξ2 w1 w2) :=
  sorry

/-- The inverse image `(E' ⟶ V)⁻¹ Z` as a closed subset of `E'` over `V`. -/
def sliceClosed (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    Closeds (Points (sliceSpace ξ1 ξ2 w1 w2)) :=
  ((of ξ1 ξ2 w1 w2).closed.preimage
      (Points.continuous_map (of ξ1 ξ2 w1 w2).toV)).preimage
    (continuous_pointsSlice (of ξ1 ξ2 w1 w2).space (of ξ1 ξ2 w1 w2).toV)

/-- The fibre of `E_W` over `V`. -/
def sliceFormal (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    (Over V.left)ᵒᵖ ⥤ Type u :=
  Scheme.Over.fiberFunctor (toOver (of ξ1 ξ2 w1 w2))
    (yonedaEquiv (𝟙 (ofOver V)))

/-- The fibre of `E_W` over `V` is a formal algebraic space. -/
theorem instIsFormal_sliceFormal (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    FormalAlgebraicSpace.IsFormalAlgebraicSpace (sliceFormal ξ1 ξ2 w1 w2) :=
  sorry

/-- The fibre of `E_W` over `V` is locally Noetherian. -/
theorem instIsLocallyNoetherian_sliceFormal (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    @FormalAlgebraicSpace.IsLocallyNoetherian _ (sliceFormal ξ1 ξ2 w1 w2)
      (instIsFormal_sliceFormal ξ1 ξ2 w1 w2) :=
  sorry

/-- Completing a slice section along `(E' ⟶ V)⁻¹ Z` yields a completion of
`E'` along the inverse image of `Z`. -/
private theorem sliceFactor_mapsInto (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx)
    {U : (Over V.left)ᵒᵖ}
    (x : (completionAlong (sliceSpace ξ1 ξ2 w1 w2)
      (sliceClosed ξ1 ξ2 w1 w2)).obj U) :
    mapsInto
      (((of ξ1 ξ2 w1 w2).closed.preimage
          (Points.continuous_map (of ξ1 ξ2 w1 w2).toV) : Closeds _) : Set _)
      (x.1).1 :=
  sorry

/-- The image of `sliceFactor` in `E_W` lies over the structure morphism of
`T`. -/
private theorem sliceFactor_liesOver (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx)
    {U : (Over V.left)ᵒᵖ}
    (x : (completionAlong (sliceSpace ξ1 ξ2 w1 w2)
      (sliceClosed ξ1 ξ2 w1 w2)).obj U) :
    (toOver (of ξ1 ξ2 w1 w2)).app (op ((Over.map V.hom).obj U.unop))
        ((of ξ1 ξ2 w1 w2).factor.app (op ((Over.map V.hom).obj U.unop))
          ⟨(x.1).1, sliceFactor_mapsInto ξ1 ξ2 w1 w2 x⟩) =
      yonedaEquiv (ofOverMap (Scheme.Over.fromOver U.unop)) :=
  sorry

/-- The restriction of `E'_{/Z} ⟶ E_W` to schemes over `V`. -/
def sliceFactor (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    completionAlong (sliceSpace ξ1 ξ2 w1 w2) (sliceClosed ξ1 ξ2 w1 w2) ⟶
      sliceFormal ξ1 ξ2 w1 w2 where
  app U := ofHom fun x ↦
    ⟨(of ξ1 ξ2 w1 w2).factor.app (op ((Over.map V.hom).obj U.unop))
        ⟨(x.1).1, by exact sliceFactor_mapsInto ξ1 ξ2 w1 w2 x⟩,
      by exact sliceFactor_liesOver ξ1 ξ2 w1 w2 x⟩
  naturality := sorry

/-- The reduction of the fibre of `E_W` is locally of finite type over `V`. -/
theorem instLocallyOfFiniteType_sliceReduction (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    LocallyOfFiniteType
      (toBase (@FormalAlgebraicSpace.reductionSpace V.left (sliceFormal ξ1 ξ2 w1 w2)
        (instIsFormal_sliceFormal ξ1 ξ2 w1 w2)
        (instIsLocallyNoetherian_sliceFormal ξ1 ξ2 w1 w2))) :=
  sorry

/-- The comparison over `V` is locally of finite type. -/
theorem instLocallyOfFiniteType_sliceFactor (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    FormalAlgebraicSpace.LocallyOfFiniteType (sliceFactor ξ1 ξ2 w1 w2) :=
  sorry

/-- The comparison over `V` is a formal modification. -/
theorem instFormalModification_sliceFactor (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    @FormalAlgebraicSpace.FormalModification V.left
      (completionAlong (sliceSpace ξ1 ξ2 w1 w2) (sliceClosed ξ1 ξ2 w1 w2)) (sliceFormal ξ1 ξ2 w1 w2)
      (sliceFactor ξ1 ξ2 w1 w2)
      (instIsFormalAlgebraicSpace_completionAlong (sliceSpace ξ1 ξ2 w1 w2) (sliceClosed ξ1 ξ2 w1 w2))
      (instIsFormal_sliceFormal ξ1 ξ2 w1 w2)
      (@instIsLocallyNoetherian_completionAlong V.left (sliceSpace ξ1 ξ2 w1 w2)
        (instIsLocallyNoetherian_sliceSpace ξ1 ξ2 w1 w2) (sliceClosed ξ1 ξ2 w1 w2))
      (instIsLocallyNoetherian_sliceFormal ξ1 ξ2 w1 w2) (instLocallyOfFiniteType_sliceFactor ξ1 ξ2 w1 w2) :=
  sorry

/-- The contraction situation over `V` with algebraic space `E'` over `V`,
closed subset `(E' ⟶ V)⁻¹ Z`, formal algebraic space the fibre of `E_W`, and
comparison the restriction of `factor`. -/
def toSituation (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    ContractionSituation V.left where
  X' := sliceSpace ξ1 ξ2 w1 w2
  locallyOfFiniteType_X' := instLocallyOfFiniteType_sliceSpace ξ1 ξ2 w1 w2
  isLocallyNoetherian_X' := instIsLocallyNoetherian_sliceSpace ξ1 ξ2 w1 w2
  T' := sliceClosed ξ1 ξ2 w1 w2
  W := sliceFormal ξ1 ξ2 w1 w2
  isFormal_W := instIsFormal_sliceFormal ξ1 ξ2 w1 w2
  isLocallyNoetherian_W := instIsLocallyNoetherian_sliceFormal ξ1 ξ2 w1 w2
  reductionData_W := @FormalAlgebraicSpace.reductionData V.left
    (sliceFormal ξ1 ξ2 w1 w2) (instIsFormal_sliceFormal ξ1 ξ2 w1 w2)
    (instIsLocallyNoetherian_sliceFormal ξ1 ξ2 w1 w2)
  locallyOfFiniteType_red := instLocallyOfFiniteType_sliceReduction ξ1 ξ2 w1 w2
  g := sliceFactor ξ1 ξ2 w1 w2
  locallyOfFiniteType_g := instLocallyOfFiniteType_sliceFactor ξ1 ξ2 w1 w2
  isFormalModification := instFormalModification_sliceFactor ξ1 ξ2 w1 w2

/-- The algebraic space of `toSituation` is `E'` viewed over `V`. -/
theorem toSituation_X' (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    (toSituation ξ1 ξ2 w1 w2).X' = sliceSpace ξ1 ξ2 w1 w2 :=
  rfl

/-- The closed subset of `toSituation` is `(E' ⟶ V)⁻¹ Z`. -/
theorem toSituation_T' (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    (toSituation ξ1 ξ2 w1 w2).T' = sliceClosed ξ1 ξ2 w1 w2 :=
  rfl

/-- The formal algebraic space of `toSituation` is the fibre of `E_W` over
`V`. -/
theorem toSituation_W (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    (toSituation ξ1 ξ2 w1 w2).W = sliceFormal ξ1 ξ2 w1 w2 :=
  rfl

/-- The comparison of `toSituation` is the restriction of `factor`. -/
theorem toSituation_g (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    (toSituation ξ1 ξ2 w1 w2).g = sliceFactor ξ1 ξ2 w1 w2 :=
  rfl

/-- The two triples restrict to the same element of `F(A)` along `φ : A ⟶ V`. -/
def agrees (ξ1 ξ2 : Triple σ V) {A : Over S}
    [locallyNoetherian_A : AlgebraicGeometry.IsLocallyNoetherian A.left] (φ : A ⟶ V) : Prop :=
  Triple.map φ ξ1 = Triple.map φ ξ2

/-- Agreement of the two triples is stable under precomposition over `V`. -/
theorem agrees_restrict (ξ1 ξ2 : Triple σ V) {A B : Over V.left}
    [AlgebraicGeometry.IsLocallyNoetherian A.left]
    [AlgebraicGeometry.IsLocallyNoetherian B.left]
    (φ : B ⟶ A) (h : agrees ξ1 ξ2 (locallyNoetherian_A := ‹AlgebraicGeometry.IsLocallyNoetherian A.left›)
      (Scheme.Over.fromOver A)) :
    agrees ξ1 ξ2 (locallyNoetherian_A := ‹AlgebraicGeometry.IsLocallyNoetherian B.left›)
      (Scheme.Over.fromOver B) :=
  sorry

/-- The functor on locally Noetherian schemes over `V` sending `φ` to the
proposition `Triple.map φ ξ1 = Triple.map φ ξ2`. -/
def agreesFunctor (ξ1 ξ2 : Triple σ V) :
    (locallyNoetherian V.left).FullSubcategoryᵒᵖ ⥤ Type (u + 1) where
  obj A := ULift.{u + 1} (PLift (agrees ξ1 ξ2 (A := (Over.map V.hom).obj A.unop.obj)
      (locallyNoetherian_A := A.unop.property)
      (Scheme.Over.fromOver A.unop.obj)))
  map φ := ofHom fun x ↦
    ⟨⟨agrees_restrict ξ1 ξ2 φ.unop.hom x.down.down⟩⟩
  map_id := sorry
  map_comp := sorry

/-- Components of `agreesFunctor` are `PLift` of agreement of the restricted
triples. -/
theorem agreesFunctor_obj (ξ1 ξ2 : Triple σ V)
    (A : (locallyNoetherian V.left).FullSubcategory) :
    (agreesFunctor ξ1 ξ2).obj (op A) =
      ULift.{u + 1} (PLift (agrees ξ1 ξ2 (A := (Over.map V.hom).obj A.obj)
      (locallyNoetherian_A := A.property)
      (Scheme.Over.fromOver A.obj))) :=
  rfl

end DiagonalEqualizer

variable {σ : ContractionSituation S} {V : Over S}
  [AlgebraicGeometry.IsLocallyNoetherian V.left]
variable (ξ1 ξ2 : Triple σ V)
variable (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
variable (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx)

/-- The open restriction of the interpolating equalizer is a monomorphism and equalizes the two open maps universally. -/
theorem openRestrict_mono :
    Mono (DiagonalEqualizer.openPullbackSnd (DiagonalEqualizer.of ξ1 ξ2 w1 w2)) ∧
      DiagonalEqualizer.openRestrict ξ1 ξ2 w1 w2 ≫
          openComplementAlong.mapOfLe
            (inf_le_sup : ξ1.Z ⊓ ξ2.Z ≤ ξ1.Z ⊔ ξ2.Z) =
        DiagonalEqualizer.openPullbackSnd
          (DiagonalEqualizer.of ξ1 ξ2 w1 w2) ∧
      IsPullback
        (DiagonalEqualizer.openRestrict ξ1 ξ2 w1 w2 ≫
          DiagonalEqualizer.leftOpen ξ1 ξ2)
        (DiagonalEqualizer.openRestrict ξ1 ξ2 w1 w2)
        (prod.lift (𝟙 σ.openComplement) (𝟙 σ.openComplement))
        (prod.lift (DiagonalEqualizer.leftOpen ξ1 ξ2)
          (DiagonalEqualizer.rightOpen ξ1 ξ2)) :=
  sorry

/-- Two compatible triples agree after restriction if and only if their open and completed structure maps factor through the corresponding equalizers. -/
theorem restricts_iff_factors {A : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian A.left] (φ : A ⟶ V) :
    DiagonalEqualizer.agrees ξ1 ξ2 φ ↔
      (∃ h : openComplementAlong (ofOver A)
            ((DiagonalEqualizer.of ξ1 ξ2 w1 w2).closed.preimage
              (Points.continuous_map (ofOverMap φ))) ⟶
          DiagonalEqualizer.openPullback (DiagonalEqualizer.of ξ1 ξ2 w1 w2),
        h ≫ DiagonalEqualizer.openPullbackSnd
            (DiagonalEqualizer.of ξ1 ξ2 w1 w2) =
          openComplementAlong.map (ofOverMap φ)
            (DiagonalEqualizer.of ξ1 ξ2 w1 w2).closed) ∧
      (∃ k : completionAlong (ofOver A)
            ((DiagonalEqualizer.of ξ1 ξ2 w1 w2).closed.preimage
              (Points.continuous_map (ofOverMap φ))) ⟶
          (DiagonalEqualizer.of ξ1 ξ2 w1 w2).formal,
        k ≫ (DiagonalEqualizer.of ξ1 ξ2 w1 w2).toFormal =
          completionAlong.map (ofOverMap φ)
            (DiagonalEqualizer.of ξ1 ξ2 w1 w2).closed) :=
  sorry

/-- A morphism into a solution over `V` forces the two triples to agree. -/
theorem agrees_of_solutionHom (E : AlgebraicSpace V.left)
    [LocallyOfFiniteType (toBase E)]
    (sol : SolutionFor (DiagonalEqualizer.toSituation ξ1 ξ2 w1 w2) E)
    {A : (locallyNoetherian V.left).FullSubcategory}
    (f : ofOver A.obj ⟶ E) :
    DiagonalEqualizer.agrees ξ1 ξ2 (A := (Over.map V.hom).obj A.obj)
      (locallyNoetherian_A := A.property)
      (Scheme.Over.fromOver A.obj) :=
  sorry

/-- The comparison from morphisms into a solution to agreement of the two
triples, on locally Noetherian schemes over `V`. -/
def diagonalFiberHom (E : AlgebraicSpace V.left)
    [LocallyOfFiniteType (toBase E)]
    (sol : SolutionFor (DiagonalEqualizer.toSituation ξ1 ξ2 w1 w2) E) :
    homOnLocallyNoetherian E ⟶ DiagonalEqualizer.agreesFunctor ξ1 ξ2 where
  app A := ofHom fun f ↦ ⟨⟨agrees_of_solutionHom ξ1 ξ2 w1 w2 E sol f⟩⟩
  naturality := sorry

/-- A solution of the equalizer contraction situation represents the diagonal fiber of the contraction functor on locally Noetherian schemes. -/
@[stacks 0GHD]
theorem represents_diagonalFiber (E : AlgebraicSpace V.left)
    [LocallyOfFiniteType (toBase E)]
    (sol : SolutionFor (DiagonalEqualizer.toSituation ξ1 ξ2 w1 w2) E) :
    IsIso (diagonalFiberHom ξ1 ξ2 w1 w2 E sol) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
