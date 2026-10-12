/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

/-!
# Affine stages of an I-adic formal spectrum

The `ℕ`-indexed diagram of affine thickenings `Spec(A ⧸ I ^ (n + 1))` over a
scheme `S`, and its Yoneda colimit. This is the functor-of-points form of
`Spf` of the `I`-adic completion of `A`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The affine stage `Spec(A ⧸ I ^ (n + 1))` over `S`. -/
def powerStage {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) ≫
    structureHom)

/-- The underlying scheme of `powerStage structureHom I n` is
`Spec(A ⧸ I ^ (n + 1))`. -/
theorem powerStage_left {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    (powerStage structureHom I n).left = Spec (.of (A ⧸ I ^ (n + 1))) :=
  sorry

/-- Each power stage is affine. -/
instance powerStage_isAffine {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    IsAffine (powerStage structureHom I n).left :=
  sorry

/-- The morphism of schemes over `S` from the `n`-th power stage to `Spec(A)`. -/
def powerStageToSpec {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    powerStage structureHom I n ⟶ Over.mk structureHom :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) rfl

/-- The underlying scheme morphism of `powerStageToSpec` is `Spec` of the
quotient map `A →+* A ⧸ I ^ (n + 1)`. -/
theorem powerStageToSpec_left {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    (powerStageToSpec structureHom I n).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) :=
  sorry

/-- The morphism `Spec(A ⧸ I ^ (n + 1)) ⟶ Spec(A)` is a thickening. -/
instance powerStageToSpec_isThickening {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    IsThickening (powerStageToSpec structureHom I n).left :=
  sorry

/-- The diagram of affine thickenings `Spec(A ⧸ I ^ (n + 1))` indexed by `ℕ`. -/
def powerThickenings {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) : ℕ ⥤ Over S where
  obj n := powerStage structureHom I n
  map {m n} f :=
    Over.homMk
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factorPow I (Nat.succ_le_succ (leOfHom f)))))
      sorry
  map_id := sorry
  map_comp := sorry

/-- Objects of `powerThickenings structureHom I` are the stages
`powerStage structureHom I n`. -/
theorem powerThickenings_obj {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    (powerThickenings structureHom I).obj n = powerStage structureHom I n :=
  sorry

/-- Transition maps of `powerThickenings structureHom I` are thickenings. -/
instance powerThickenings_map_isThickening {S : Scheme.{u}} {A : Type u}
    [CommRing A] (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) {m n : ℕ}
    (f : m ⟶ n) :
    IsThickening ((powerThickenings structureHom I).map f).left :=
  sorry

/-- The formal spectrum of the `I`-adic completion of `A` over `S`, as the
Yoneda colimit of `Spec(A ⧸ I ^ (n + 1))`. -/
def spfAdicCompletion {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) : (Over S)ᵒᵖ ⥤ Type u :=
  colimit (powerThickenings structureHom I ⋙ yoneda)

/-- `spfAdicCompletion structureHom I` is the Yoneda colimit of
`powerThickenings structureHom I`. -/
theorem spfAdicCompletion_eq {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    spfAdicCompletion structureHom I =
      colimit (powerThickenings structureHom I ⋙ yoneda) :=
  sorry

/-- The cocone leg from the `n`-th power stage into
`spfAdicCompletion structureHom I`. -/
def spfAdicCompletionι {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    yoneda.obj (powerStage structureHom I n) ⟶
      spfAdicCompletion structureHom I :=
  colimit.ι (powerThickenings structureHom I ⋙ yoneda) n

/-- `spfAdicCompletionι structureHom I n` is the colimit cocone component at
`n`. -/
theorem spfAdicCompletionι_eq {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (n : ℕ) :
    spfAdicCompletionι structureHom I n =
      colimit.ι (powerThickenings structureHom I ⋙ yoneda) n :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
