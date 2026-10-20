module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeFunctor

/-!
# Fibers over schemes of a morphism of algebraic spaces

Schemes over the target determine categorical pullbacks, and morphisms of test
schemes induce canonical maps between those fibers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Schemes over an algebraic space `B`, as costructured arrows of `ofOverFunctor S`. -/
abbrev SchemesOver (B : AlgebraicSpace S) :=
  CostructuredArrow (ofOverFunctor S) B

/-- The base change `X_T = T ×_B X` of `X` along a scheme `T` over `B`. -/
def fiber (f : X ⟶ B) (σ : SchemesOver B) : AlgebraicSpace S :=
  pullback f σ.hom

/-- The projection `X_T ⟶ T` of the fibre product, as a morphism of algebraic spaces. -/
def fiberToBase (f : X ⟶ B) (σ : SchemesOver B) :
    fiber f σ ⟶ (ofOverFunctor S).obj σ.left :=
  pullback.snd f σ.hom

/-- The canonical map `X_T ⟶ X_{T'}` induced by a morphism of schemes over `B`. -/
def fiberMap (f : X ⟶ B) {σ τ : SchemesOver B} (h : σ ⟶ τ) :
    fiber f σ ⟶ fiber f τ :=
  pullback.map f σ.hom f τ.hom (𝟙 X) ((ofOverFunctor S).map h.left) (𝟙 B)
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    ((Category.comp_id σ.hom).trans (CostructuredArrow.w h).symm)

/-- The map `fiberMap f h` commutes with the projections to `X`. -/
theorem fiberMap_fst (f : X ⟶ B) {σ τ : SchemesOver B} (h : σ ⟶ τ) :
    fiberMap f h ≫ pullback.fst f τ.hom = pullback.fst f σ.hom := sorry

/-- The map `fiberMap f h` commutes with the projections to the varying base. -/
theorem fiberMap_snd (f : X ⟶ B) {σ τ : SchemesOver B} (h : σ ⟶ τ) :
    fiberMap f h ≫ pullback.snd f τ.hom =
      pullback.snd f σ.hom ≫ (ofOverFunctor S).map h.left := sorry

/-- `fiberMap f (𝟙 σ)` is the identity on the fibre, by uniqueness of maps into
a pullback together with `yoneda.map_id`. -/
def fiberMap_id_eq (f : X ⟶ B) (σ : SchemesOver B) :
    fiberMap f (𝟙 σ) = 𝟙 (fiber f σ) :=
  pullback.hom_ext
    (((pullback.lift_fst _ _ _).trans (Category.comp_id (pullback.fst f σ.hom))).trans
      (Category.id_comp (pullback.fst f σ.hom)).symm)
    (((pullback.lift_snd _ _ _).trans
        ((congrArg (fun i => pullback.snd f σ.hom ≫ i)
            (CategoryTheory.Functor.map_id yoneda σ.left)).trans
          (Category.comp_id (pullback.snd f σ.hom)))).trans
      (Category.id_comp (pullback.snd f σ.hom)).symm)

/-- `fiberMap` is functorial on morphisms of schemes over `B`, by uniqueness of
maps into a pullback together with `yoneda.map_comp`. -/
def fiberMap_comp_eq (f : X ⟶ B) {σ τ ρ : SchemesOver B} (h : σ ⟶ τ) (k : τ ⟶ ρ) :
    fiberMap f (h ≫ k) = fiberMap f h ≫ fiberMap f k :=
  pullback.hom_ext
    (Eq.trans
      (Eq.trans (pullback.lift_fst _ _ _) (Category.comp_id (pullback.fst f σ.hom)))
      (Eq.symm
        (Eq.trans
          (Eq.symm (Category.assoc (fiberMap f h) (fiberMap f k) (pullback.fst f ρ.hom)))
          (Eq.trans
            (congrArg (fun φ => fiberMap f h ≫ φ)
              (Eq.trans (pullback.lift_fst _ _ _)
                (Category.comp_id (pullback.fst f τ.hom))))
            (Eq.trans (pullback.lift_fst _ _ _)
              (Category.comp_id (pullback.fst f σ.hom)))))))
    (Eq.trans (pullback.lift_snd _ _ _)
      (Eq.trans
        (congrArg (fun i => pullback.snd f σ.hom ≫ i)
          (CategoryTheory.Functor.map_comp yoneda h.left k.left))
        (Eq.trans
          (Eq.symm
            (Category.assoc (pullback.snd f σ.hom) ((ofOverFunctor S).map h.left)
              ((ofOverFunctor S).map k.left)))
          (Eq.trans
            (congrArg (fun φ => φ ≫ (ofOverFunctor S).map k.left)
              (Eq.symm (pullback.lift_snd _ _ _)))
            (Eq.trans
              (Category.assoc (fiberMap f h) (pullback.snd f τ.hom)
                ((ofOverFunctor S).map k.left))
              (Eq.trans
                (congrArg (fun φ => fiberMap f h ≫ φ)
                  (Eq.symm (pullback.lift_snd _ _ _)))
                (Category.assoc (fiberMap f h) (fiberMap f k)
                  (pullback.snd f ρ.hom))))))))

variable {Y : AlgebraicSpace S}

/-- The comparison `X_T ⟶ Y_T` induced by `π : X ⟶ Y` over `B`. -/
def fiberComparison (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemesOver B) :
    fiber (π ≫ y) σ ⟶ fiber y σ :=
  pullback.map (π ≫ y) σ.hom y σ.hom π
    (𝟙 ((ofOverFunctor S).obj σ.left)) (𝟙 B) (Category.comp_id (π ≫ y))
    ((Category.comp_id σ.hom).trans (Category.id_comp σ.hom).symm)

/-- The fibre comparison commutes with the projections to `X` and `Y`. -/
theorem fiberComparison_fst (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemesOver B) :
    fiberComparison π y σ ≫ pullback.fst y σ.hom =
      pullback.fst (π ≫ y) σ.hom ≫ π :=
  pullback.lift_fst _ _ _

/-- The fibre comparison commutes with the projections to the test scheme. -/
theorem fiberComparison_snd (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemesOver B) :
    fiberComparison π y σ ≫ pullback.snd y σ.hom =
      pullback.snd (π ≫ y) σ.hom ≫ 𝟙 ((ofOverFunctor S).obj σ.left) :=
  pullback.lift_snd _ _ _

/-- The fibre comparison is the map of pullbacks induced by `π` and the identity
on the test scheme. -/
theorem fiberComparison_spec (π : X ⟶ Y) (y : Y ⟶ B) (σ : SchemesOver B) :
    fiberComparison π y σ ≫ pullback.fst y σ.hom =
        pullback.fst (π ≫ y) σ.hom ≫ π ∧
      fiberComparison π y σ ≫ pullback.snd y σ.hom =
        pullback.snd (π ≫ y) σ.hom :=
  ⟨fiberComparison_fst π y σ,
    (fiberComparison_snd π y σ).trans
      (Category.comp_id (pullback.snd (π ≫ y) σ.hom))⟩

/-- First-projection compatibility of the fibre comparison square. -/
private theorem fiberComparison_comm_fst (π : X ⟶ Y) (y : Y ⟶ B)
    {σ τ : SchemesOver B} (h : σ ⟶ τ) :
    (fiberMap (π ≫ y) h ≫ fiberComparison π y τ) ≫ pullback.fst y τ.hom =
      (fiberComparison π y σ ≫ fiberMap y h) ≫ pullback.fst y τ.hom :=
  Eq.trans
    (Eq.trans (Category.assoc _ _ _)
      (Eq.trans
        (congrArg (fun φ => fiberMap (π ≫ y) h ≫ φ) (fiberComparison_fst π y τ))
        (Eq.trans (Eq.symm (Category.assoc _ _ _))
          (congrArg (fun φ => φ ≫ π)
            ((pullback.lift_fst _ _ _).trans
              (Category.comp_id (pullback.fst (π ≫ y) σ.hom)))))))
    (Eq.symm
      (Eq.trans (Category.assoc _ _ _)
        (Eq.trans
          (congrArg (fun φ => fiberComparison π y σ ≫ φ)
            ((pullback.lift_fst _ _ _).trans (Category.comp_id (pullback.fst y σ.hom))))
          (fiberComparison_fst π y σ))))

/-- Second-projection compatibility of the fibre comparison square. -/
private theorem fiberComparison_comm_snd (π : X ⟶ Y) (y : Y ⟶ B)
    {σ τ : SchemesOver B} (h : σ ⟶ τ) :
    (fiberMap (π ≫ y) h ≫ fiberComparison π y τ) ≫ pullback.snd y τ.hom =
      (fiberComparison π y σ ≫ fiberMap y h) ≫ pullback.snd y τ.hom :=
  Eq.trans
    (Eq.trans (Category.assoc _ _ _)
      (Eq.trans
        (congrArg (fun φ => fiberMap (π ≫ y) h ≫ φ) (fiberComparison_snd π y τ))
        (Eq.trans
          (congrArg (fun φ => fiberMap (π ≫ y) h ≫ φ)
            (Category.comp_id (pullback.snd (π ≫ y) τ.hom)))
          (pullback.lift_snd _ _ _))))
    (Eq.symm
      (Eq.trans (Category.assoc _ _ _)
        (Eq.trans
          (congrArg (fun φ => fiberComparison π y σ ≫ φ) (pullback.lift_snd _ _ _))
          (Eq.trans (Eq.symm (Category.assoc _ _ _))
            (Eq.trans
              (congrArg (fun φ => φ ≫ (ofOverFunctor S).map h.left)
                (fiberComparison_snd π y σ))
              (congrArg (fun φ => φ ≫ (ofOverFunctor S).map h.left)
                (Category.comp_id (pullback.snd (π ≫ y) σ.hom))))))))

/-- The fibre comparison square commutes. -/
theorem fiberComparison_comm (π : X ⟶ Y) (y : Y ⟶ B)
    {σ τ : SchemesOver B} (h : σ ⟶ τ) :
    fiberMap (π ≫ y) h ≫ fiberComparison π y τ =
      fiberComparison π y σ ≫ fiberMap y h :=
  pullback.hom_ext (fiberComparison_comm_fst π y h) (fiberComparison_comm_snd π y h)

/-- The fibre comparison square is a pullback. -/
theorem fiberComparison_isPullback (π : X ⟶ Y) (y : Y ⟶ B)
    {σ τ : SchemesOver B} (h : σ ⟶ τ) :
    IsPullback (fiberMap (π ≫ y) h) (fiberComparison π y σ)
      (fiberComparison π y τ) (fiberMap y h) := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
