module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import ReasLib.AlgebraicGeometry.Scheme.DescentData
public import stacks_project.Chap85.Definition_85_27_1_Cartesian
public import stacks_project.Chap85.Definition_85_27_3_Nerve

/-!
# Descent data from a cartesian morphism over a Čech nerve

A cartesian morphism `π : Y ⟶ (X/S)_•` determines `V = Y _⦋0⦌` as a scheme over `X`
and comparison isomorphisms `Y _⦋1⦌ ≅ V ×_S X` and `Y _⦋1⦌ ≅ X ×_S V`, hence an
isomorphism `φ : V ×_S X ≅ X ×_S V` over `X ×_S X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Simplicial
open CategoryTheory.SimplicialObject CategoryTheory.Arrow

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.DescentData

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable {Y : SimplicialObject Scheme.{u}} (π : Y ⟶ f.simplicialScheme)

/-- The degree-zero scheme `V = Y _⦋0⦌`, viewed as a scheme over `X` via `π.app (op ⦋0⦌)`
and the identification `(X/S)_0 ≅ X`. -/
def schemeOver : Over X :=
  Over.mk (π.app (op ⦋0⦌) ≫ (cechNerve.degreeZero.iso (Arrow.mk f)).hom)

/-- The underlying scheme of `schemeOver f π` is `Y _⦋0⦌`. -/
theorem schemeOver_left : (schemeOver f π).left = Y _⦋0⦌ := sorry

/-- The structure morphism of `schemeOver f π` is `π.app (op ⦋0⦌)` followed by the
degree-zero Čech identification. -/
theorem schemeOver_hom :
    (schemeOver f π).hom =
      π.app (op ⦋0⦌) ≫ (cechNerve.degreeZero.iso (Arrow.mk f)).hom := sorry

/-- Čech identification of the `δ 1` cospan with the cospan for `V ×_X (X ×_S X)`. -/
def faceOneCechIso :
    pullback (f.simplicialScheme.δ (1 : Fin 2)) (π.app (op ⦋0⦌)) ≅
      pullback (pullback.fst f f) (schemeOver f π).hom where
  hom :=
    pullback.map (f.simplicialScheme.δ (1 : Fin 2)) (π.app (op ⦋0⦌))
      (pullback.fst f f) (schemeOver f π).hom
      (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).hom (𝟙 _)
      (cechNerve.degreeZero.iso (Arrow.mk f)).hom sorry sorry
  inv :=
    pullback.map (pullback.fst f f) (schemeOver f π).hom
      (f.simplicialScheme.δ (1 : Fin 2)) (π.app (op ⦋0⦌))
      (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).inv (𝟙 _)
      (cechNerve.degreeZero.iso (Arrow.mk f)).inv sorry sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The source map `(Y.δ 1, pr₁ ∘ π₁) : Y _⦋1⦌ ⟶ V ×_S X`. -/
def faceOneIso [hπ : IsCartesian π] :
    Y _⦋1⦌ ≅ pullback ((schemeOver f π).hom ≫ f) f where
  hom :=
    pullback.lift (Y.δ (1 : Fin 2))
      (π.app (op ⦋1⦌) ≫ cechNerve.degreeOne.snd (Arrow.mk f)) sorry
  inv :=
    ((hπ.isPullback (SimplexCategory.δ (1 : Fin 2))).isoPullback ≪≫
        faceOneCechIso f π ≪≫
        pullbackSymmetry (pullback.fst f f) (schemeOver f π).hom ≪≫
        pullbackRightPullbackFstIso f f (schemeOver f π).hom).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The first projection of `faceOneIso` is the face `Y.δ 1`. -/
theorem faceOneIso_hom_fst [IsCartesian π] :
    (faceOneIso f π).hom ≫ pullback.fst ((schemeOver f π).hom ≫ f) f =
      Y.δ (1 : Fin 2) := sorry

/-- The second projection of `faceOneIso` is `pr₁ ∘ π₁`. -/
theorem faceOneIso_hom_snd [IsCartesian π] :
    (faceOneIso f π).hom ≫ pullback.snd ((schemeOver f π).hom ≫ f) f =
      π.app (op ⦋1⦌) ≫ cechNerve.degreeOne.snd (Arrow.mk f) := sorry

/-- Čech identification of the `δ 0` cospan with the cospan for `(X ×_S X) ×_X V`. -/
def faceZeroCechIso :
    pullback (f.simplicialScheme.δ (0 : Fin 2)) (π.app (op ⦋0⦌)) ≅
      pullback (pullback.snd f f) (schemeOver f π).hom where
  hom :=
    pullback.map (f.simplicialScheme.δ (0 : Fin 2)) (π.app (op ⦋0⦌))
      (pullback.snd f f) (schemeOver f π).hom
      (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).hom (𝟙 _)
      (cechNerve.degreeZero.iso (Arrow.mk f)).hom sorry sorry
  inv :=
    pullback.map (pullback.snd f f) (schemeOver f π).hom
      (f.simplicialScheme.δ (0 : Fin 2)) (π.app (op ⦋0⦌))
      (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).inv (𝟙 _)
      (cechNerve.degreeZero.iso (Arrow.mk f)).inv sorry sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The source map `(pr₀ ∘ π₁, Y.δ 0) : Y _⦋1⦌ ⟶ X ×_S V`. -/
def faceZeroIso [hπ : IsCartesian π] :
    Y _⦋1⦌ ≅ pullback f ((schemeOver f π).hom ≫ f) where
  hom :=
    pullback.lift (π.app (op ⦋1⦌) ≫ cechNerve.degreeOne.fst (Arrow.mk f))
      (Y.δ (0 : Fin 2)) sorry
  inv :=
    ((hπ.isPullback (SimplexCategory.δ (0 : Fin 2))).isoPullback ≪≫
        faceZeroCechIso f π ≪≫
        pullbackLeftPullbackSndIso f f (schemeOver f π).hom).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The first projection of `faceZeroIso` is `pr₀ ∘ π₁`. -/
theorem faceZeroIso_hom_fst [IsCartesian π] :
    (faceZeroIso f π).hom ≫ pullback.fst f ((schemeOver f π).hom ≫ f) =
      π.app (op ⦋1⦌) ≫ cechNerve.degreeOne.fst (Arrow.mk f) := sorry

/-- The second projection of `faceZeroIso` is the face `Y.δ 0`. -/
theorem faceZeroIso_hom_snd [IsCartesian π] :
    (faceZeroIso f π).hom ≫ pullback.snd f ((schemeOver f π).hom ≫ f) =
      Y.δ (0 : Fin 2) := sorry

/-- The resulting isomorphism `φ : V ×_S X ≅ X ×_S V`. -/
def iso [IsCartesian π] :
    pullback ((schemeOver f π).hom ≫ f) f ≅
      pullback f ((schemeOver f π).hom ≫ f) :=
  (faceOneIso f π).symm ≪≫ faceZeroIso f π

/-- `iso f π` is the composite of the two displayed face identifications. -/
theorem iso_eq [IsCartesian π] :
    iso f π = (faceOneIso f π).symm ≪≫ faceZeroIso f π := sorry

/-- The left morphism of the comparison of face pullbacks of `V` over `X ×_S X`. -/
def overIso_left [IsCartesian π] :
    pullback (schemeOver f π).hom (pullback.fst f f) ≅
      pullback (schemeOver f π).hom (pullback.snd f f) :=
  pullbackRightPullbackFstIso f f (schemeOver f π).hom ≪≫
    iso f π ≪≫
    (pullbackLeftPullbackSndIso f f (schemeOver f π).hom).symm ≪≫
    pullbackSymmetry (pullback.snd f f) (schemeOver f π).hom

/-- The isomorphism `φ` as a morphism of schemes over `X ×_S X`. -/
def overIso [IsCartesian π] :
    (Over.pullback (pullback.fst f f)).obj (schemeOver f π) ≅
      (Over.pullback (pullback.snd f f)).obj (schemeOver f π) :=
  Over.isoMk (overIso_left f π) sorry

/-- The left morphism of `overIso` is `overIso_left`. -/
theorem overIso_hom_left [IsCartesian π] :
    (overIso f π).hom.left = (overIso_left f π).hom := sorry

/-- Reidentify `Over.pullback` along an equality of base morphisms. -/
def recodePullback {A B : Scheme.{u}} {g h : A ⟶ B} (e : g = h) :
    Over.pullback g ≅ Over.pullback h :=
  eqToIso (congrArg (fun t ↦ Over.pullback t) e)

/-- The descent comparison over a test object `Y'` with a pair of maps to `X` over `S`. -/
def comparisonHom [IsCartesian π] {Y' : Scheme.{u}} (g₁ g₂ : Y' ⟶ X)
    (hg : g₁ ≫ f = g₂ ≫ f) :
    (Over.pullback g₁).obj (schemeOver f π) ⟶
      (Over.pullback g₂).obj (schemeOver f π) :=
  (recodePullback (pullback.lift_fst g₁ g₂ hg).symm).hom.app (schemeOver f π) ≫
    (Over.pullbackComp (pullback.lift g₁ g₂ hg) (pullback.fst f f)).hom.app
      (schemeOver f π) ≫
    (Over.pullback (pullback.lift g₁ g₂ hg)).map (overIso f π).hom ≫
    (Over.pullbackComp (pullback.lift g₁ g₂ hg) (pullback.snd f f)).inv.app
      (schemeOver f π) ≫
    (recodePullback (pullback.lift_snd g₁ g₂ hg)).hom.app (schemeOver f π)

/-- `recodePullback` along `rfl` is the identity functor isomorphism. -/
theorem recodePullback_refl {A B : Scheme.{u}} (g : A ⟶ B) :
    recodePullback (rfl : g = g) = Iso.refl (Over.pullback g) := sorry

/-- The first projection of `faceOneCechIso` is the degree-one Čech comparison. -/
theorem faceOneCechIso_hom_fst :
    (faceOneCechIso f π).hom ≫ pullback.fst (pullback.fst f f) (schemeOver f π).hom =
      pullback.fst (f.simplicialScheme.δ (1 : Fin 2)) (π.app (op ⦋0⦌)) ≫
        (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).hom := sorry

/-- The first projection of `faceZeroCechIso` is the degree-one Čech comparison. -/
theorem faceZeroCechIso_hom_fst :
    (faceZeroCechIso f π).hom ≫ pullback.fst (pullback.snd f f) (schemeOver f π).hom =
      pullback.fst (f.simplicialScheme.δ (0 : Fin 2)) (π.app (op ⦋0⦌)) ≫
        (cechNerve.degreeOne.pullbackIso (Arrow.mk f)).hom := sorry

/-- `comparisonHom` along a repeated map to `X` is the identity. -/
theorem comparisonHom_self [IsCartesian π] {Y' : Scheme.{u}} (g : Y' ⟶ X) :
    comparisonHom f π g g rfl = 𝟙 _ := sorry

/-- `overIso_left` pastes the binary comparison `iso` with the two fibre-product identifications. -/
theorem overIso_left_eq [IsCartesian π] :
    overIso_left f π =
      pullbackRightPullbackFstIso f f (schemeOver f π).hom ≪≫
        iso f π ≪≫
        (pullbackLeftPullbackSndIso f f (schemeOver f π).hom).symm ≪≫
        pullbackSymmetry (pullback.snd f f) (schemeOver f π).hom := sorry

end AlgebraicGeometry.Scheme.DescentData
