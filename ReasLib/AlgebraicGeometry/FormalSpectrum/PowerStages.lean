module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.FormalSpace.AdicDiagram

/-!
# Affine stages of an I-adic formal spectrum

The `ℕ`-indexed diagram of affine thickenings `Spec(A ⧸ I ^ (n + 1))` over a
scheme `S`, and its Yoneda colimit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The affine stage `Spec(A ⧸ I ^ (n + 1))` over the base scheme. -/
def powerStage {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) : Over S :=
  AdicPresentation.stage structureHom I n

/-- The underlying scheme of `powerStage structureHom I n` is the corresponding
quotient spectrum. -/
theorem powerStage_left {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    (powerStage structureHom I n).left = Spec (.of (A ⧸ I ^ (n + 1))) :=
  sorry

/-- Each power stage is affine. -/
instance powerStage_isAffine {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    IsAffine (powerStage structureHom I n).left :=
  sorry

/-- The morphism from the `n`-th power stage to `Spec(A)` over `S`. -/
def powerStageToSpec {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    powerStage structureHom I n ⟶ Over.mk structureHom :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) rfl

/-- The underlying scheme morphism of `powerStageToSpec` is induced by the
quotient map `A →+* A ⧸ I ^ (n + 1)`. -/
theorem powerStageToSpec_left {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    (powerStageToSpec structureHom I n).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) :=
  sorry

/-- The morphism from a power stage to `Spec(A)` is a closed immersion. -/
instance powerStageToSpec_isClosedImmersion {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    IsClosedImmersion (powerStageToSpec structureHom I n).left :=
  sorry

/-- The quotient-power transition commutes with the structure morphisms to the base. -/
theorem powerTransition_comm {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) {m n : ℕ} (transitionHom : m ⟶ n) :
    Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factorPow I (Nat.succ_le_succ (leOfHom transitionHom)))) ≫
      (powerStage structureHom I n).hom = (powerStage structureHom I m).hom := sorry

/-- The transition between quotient-power stages is induced by the quotient factor map. -/
def powerTransition {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) {m n : ℕ} (transitionHom : m ⟶ n) :
    powerStage structureHom I m ⟶ powerStage structureHom I n :=
  AdicPresentation.quotientMap structureHom
    (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom transitionHom)))

/-- The quotient-power transition associated to an identity is the identity. -/
theorem powerTransition_id {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    powerTransition structureHom I (𝟙 n) = 𝟙 (powerStage structureHom I n) := sorry

/-- Quotient-power transitions preserve composition. -/
theorem powerTransition_comp {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) {l m n : ℕ}
    (first : l ⟶ m) (second : m ⟶ n) :
    powerTransition structureHom I (first ≫ second) =
      powerTransition structureHom I first ≫ powerTransition structureHom I second := sorry

/-- The diagram of affine power thickenings indexed by `ℕ`. -/
def powerThickenings {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) : ℕ ⥤ Over S :=
  AdicPresentation.diagram structureHom I

/-- Objects of `powerThickenings structureHom I` are the power stages. -/
theorem powerThickenings_obj {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    (powerThickenings structureHom I).obj n = powerStage structureHom I n :=
  sorry

/-- Transition maps in the power-stage diagram are thickenings. -/
instance powerThickenings_map_isThickening {S : Scheme.{u}} {A : Type u}
    [CommRing A] (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) {m n : ℕ}
    (f : m ⟶ n) :
    IsThickening ((powerThickenings structureHom I).map f).left :=
  sorry

/-- The presheaf colimit of the power-stage Yoneda diagram. -/
def spfAdicCompletion {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) : (Over S)ᵒᵖ ⥤ Type u :=
  colimit (powerThickenings structureHom I ⋙ yoneda)

/-- The power-stage presheaf colimit unfolds to its defining colimit. -/
theorem spfAdicCompletion_eq {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    spfAdicCompletion structureHom I =
      colimit (powerThickenings structureHom I ⋙ yoneda) :=
  sorry

/-- The cocone leg from the `n`-th power stage to the presheaf colimit. -/
def spfAdicCompletionι {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    yoneda.obj (powerStage structureHom I n) ⟶
      spfAdicCompletion structureHom I :=
  colimit.ι (powerThickenings structureHom I ⋙ yoneda) n

/-- The cocone leg `spfAdicCompletionι structureHom I n` is the corresponding
colimit component. -/
theorem spfAdicCompletionι_eq {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    spfAdicCompletionι structureHom I n =
      colimit.ι (powerThickenings structureHom I ⋙ yoneda) n :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
