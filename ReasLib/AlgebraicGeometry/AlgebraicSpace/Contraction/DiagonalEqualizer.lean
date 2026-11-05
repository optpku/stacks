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
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Triple
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Product
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Separation

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Map

/-!
# Diagonal equalizers of contraction triples

Algebraic and formal equalizers of compatible contraction triples define a
contraction situation over the test scheme and characterize their agreement.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- A handle for the canonical diagonal equalizer. It stores no objects or
morphisms: every accessor below is defined by the specified limits. -/
structure DiagonalEqualizer {σ : ContractionSituation S} {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left]
    (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) where

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

variable {ξ1 ξ2 : Triple σ V}
  {w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx}
  {w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx}

/-- The canonical fibre product of the witnesses. -/
abbrev pullbackSpace (_D : DiagonalEqualizer ξ1 ξ2 w1 w2) : AlgebraicSpace S :=
  interpPullback ξ1 ξ2 w1 w2

/-- The canonical algebraic equalizer. -/
abbrev space (_D : DiagonalEqualizer ξ1 ξ2 w1 w2) : AlgebraicSpace S :=
  interpSpace ξ1 ξ2 w1 w2

/-- The canonical morphism to the test scheme. -/
abbrev toV (D : DiagonalEqualizer ξ1 ξ2 w1 w2) : D.space ⟶ ofOver V :=
  interpToV ξ1 ξ2 w1 w2

/-- The equalized morphism to `X'`. -/
abbrev spaceHom (D : DiagonalEqualizer ξ1 ξ2 w1 w2) : D.space ⟶ σ.X' :=
  pullback.fst (pairHom ξ1 ξ2 w1 w2) (diagHom σ) ≫ leftHom ξ1 ξ2 w1 w2

/-- The intersection of the two closed subsets. -/
abbrev closed (_D : DiagonalEqualizer ξ1 ξ2 w1 w2) : Closeds (Points (ofOver V)) :=
  interClosed ξ1 ξ2

/-- The canonical formal equalizer. -/
abbrev formal (_D : DiagonalEqualizer ξ1 ξ2 w1 w2) : (Over S)ᵒᵖ ⥤ Type u :=
  interpFormal ξ1 ξ2

/-- The inclusion of the formal equalizer. -/
abbrev toFormal (D : DiagonalEqualizer ξ1 ξ2 w1 w2) :
    D.formal ⟶ completionAlong (ofOver V) D.closed :=
  interpToFormal ξ1 ξ2

/-- The universal comparison from the completed algebraic equalizer. -/
abbrev factor (D : DiagonalEqualizer ξ1 ξ2 w1 w2) :
    completionAlong D.space (D.closed.preimage (Points.continuous_map D.toV)) ⟶ D.formal :=
  interpFactor ξ1 ξ2 w1 w2

/-- The handle for the specified canonical equalizer. -/
def of (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    DiagonalEqualizer ξ1 ξ2 w1 w2 := ⟨⟩

variable {ξ1 ξ2 : Triple σ V}
  {w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx}
  {w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx}

/-- The canonical fibre product is `V'_1 ×_V V'_2`. -/
theorem pullbackSpace_eq :
    (of ξ1 ξ2 w1 w2).pullbackSpace = pullback w1.toV w2.toV :=
  rfl

/-- The canonical space is the diagonal pullback of the interpolating pair. -/
theorem space_eq :
    (of ξ1 ξ2 w1 w2).space = pullback (pairHom ξ1 ξ2 w1 w2) (diagHom σ) :=
  rfl

/-- The canonical closed subset is the intersection `Z_1 ∩ Z_2`. -/
theorem closed_eq : (of ξ1 ξ2 w1 w2).closed = ξ1.Z ⊓ ξ2.Z :=
  rfl

/-- The canonical formal equalizer is the functor equalizer of `leftHat` and
`rightHat`. -/
theorem formal_eq :
    (of ξ1 ξ2 w1 w2).formal = equalizer (leftHat ξ1 ξ2) (rightHat ξ1 ξ2) :=
  rfl

/-- Postcomposing `factor` with `toFormal` recovers the completion of `toV`. -/
theorem factor_comp_ι :
    (of ξ1 ξ2 w1 w2).factor ≫ (of ξ1 ξ2 w1 w2).toFormal =
      completionAlong.map (interpToV ξ1 ξ2 w1 w2) (interClosed ξ1 ξ2) := by
  exact equalizer.lift_ι _ _

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

end DiagonalEqualizer

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
