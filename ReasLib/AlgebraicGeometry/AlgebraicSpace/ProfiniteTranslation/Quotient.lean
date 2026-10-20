module

public import Mathlib.CategoryTheory.EpiMono
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation.Presentation

/-!
# Quotient algebraic space of profinite translations

This module constructs the étale quotient sheaf of the translation action on
`Spec(LocallyConstant G k)` as an algebraic space `X = Y / Γ` over `Spec(k)`, together
with the projection `q`, the origin `k`-point `x`, and the splitting of `x`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PreRelation
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation

/-- The canonical projection from the affine presentation to its étale quotient sheaf. -/
def atlasX (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    yoneda.obj (YOver k G) ⟶ (ofAut (action k G)).smallEtaleQuotientSheaf.obj :=
  (ofAut (action k G)).smallEtaleQuotientSheafMk

/-- The atlas is the quotient projection followed by the sheafification unit. -/
theorem atlasX_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    atlasX k G = (ofAut (action k G)).smallEtaleQuotientSheafMk := by rfl

/-- The étale translation quotient sheaf satisfies fppf descent. -/
theorem functorOfPoints_isSheaf (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over (base k))
      (ofAut (action k G)).smallEtaleQuotientSheaf.obj := sorry

/-- The diagonal of the étale translation quotient sheaf is representable by schemes. -/
theorem functorOfPoints_representableDiagonal (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    yoneda.relativelyRepresentable
      (Limits.diag (ofAut (action k G)).smallEtaleQuotientSheaf.obj) := sorry

/-- The canonical projection to the translation quotient sheaf is representable and étale. -/
theorem atlasX_etale (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    (MorphismProperty.over (@Etale)).presheaf (atlasX k G) := sorry

/-- The canonical projection to the translation quotient sheaf is étale-locally surjective. -/
theorem atlasX_locallySurjective (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlasX k G) := sorry

/-- The quotient algebraic space of the affine profinite scheme by discrete translations. -/
def X (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : AlgebraicSpace (base k) :=
  ofFunctor (ofAut (action k G)).smallEtaleQuotientSheaf.obj (functorOfPoints_isSheaf k G)
    (functorOfPoints_representableDiagonal k G)
    ⟨YOver k G, atlasX k G, atlasX_etale k G, atlasX_locallySurjective k G⟩

/-- The functor of points of the translation quotient is its étale quotient sheaf. -/
theorem X_functorOfPoints (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    (X k G).functorOfPoints = (ofAut (action k G)).smallEtaleQuotientSheaf.obj := by rfl

/-- The projection `q : Y ⟶ X` of algebraic spaces over `Spec(k)`. -/
def q (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : ofOver (YOver k G) ⟶ X k G :=
  (ofAut (action k G)).smallEtaleQuotientSheafMk

/-- `q` is the quotient projection of the translation pre-relation followed by sheafification. -/
theorem q_eq (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    q k G = (ofAut (action k G)).smallEtaleQuotientSheafMk := by rfl

/-- The `k`-point `x : Spec(k) ⟶ X` induced by the origin of `G`. -/
def x (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : FieldValuedPoint (X k G) :=
  FieldValuedPoint.of k (𝟙 (base k)) (ofOverMap (originHom k G) ≫ q k G)

/-- The morphism of `x` is the composite of the origin with `q`. -/
theorem x_hom (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    (x k G).hom = ofOverMap (originHom k G) ≫ q k G := by rfl

/-- The structure morphism of `x` is the identity of `Spec(k)`. -/
theorem x_structureHom (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    (x k G).structureHom = 𝟙 (base k) := by rfl

/-- The origin `k`-point is a section of `X ⟶ Spec(k)`. -/
theorem isSection_x (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    (x k G).hom ≫ SchemeRealization.toBase (X k G) = 𝟙 (ofOver (Over.mk (𝟙 (base k)))) := by
  exact (SchemeRealization.eq_toBase _).trans (SchemeRealization.eq_toBase _).symm

/-- The splitting of `x` by the structure morphism of `X`. -/
def splitMono_x (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : SplitMono (x k G).hom where
  retraction := SchemeRealization.toBase (X k G)
  id := isSection_x k G

/-- The retraction of `splitMono_x` is the structure morphism of `X`. -/
theorem splitMono_x_retraction (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    (splitMono_x k G).retraction = SchemeRealization.toBase (X k G) := by rfl


/-- The origin field-valued point is split monic, with the structural morphism as retraction. -/
instance isSplitMono_x (k : Type u) [Field k] (G : ProfiniteGrp.{u}) :
    IsSplitMono (x k G).hom := IsSplitMono.mk' (splitMono_x k G)

/-- The origin field-valued point of the translation quotient is a monomorphism. -/
instance instMono_x (k : Type u) [Field k] (G : ProfiniteGrp.{u}) : Mono (x k G).hom :=
  inferInstance

end AlgebraicGeometry.AlgebraicSpace.ProfiniteTranslation
