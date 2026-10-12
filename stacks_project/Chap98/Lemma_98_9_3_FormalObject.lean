/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.RingTheory.Completion.LocalRing
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Formal objects of a category fibred in groupoids over `(Sch/S)_fppf`

A complete local `S`-algebra is a Noetherian complete local ring `R` equipped with
`Spec R ⟶ S` whose residue field is of finite type over `S`. A formal object of a
category fibred in groupoids `X` over `Over S` is such an algebra together with a
forward system of objects of `X` over the truncations `Spec(R ⧸ m^{n+1})`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A Noetherian complete local `S`-algebra whose residue field is of finite type over
`S`. -/
structure CompleteLocalSAlgebra (S : Scheme.{u}) : Type (u + 1) where
  /-- Underlying commutative ring. -/
  carrier : Type u
  [commRing : CommRing carrier]
  [isLocalRing : IsLocalRing carrier]
  [isNoetherianRing : IsNoetherianRing carrier]
  [isCompleteLocalRing : IsCompleteLocalRing carrier]
  /-- Structure morphism `Spec R ⟶ S`. -/
  toS : Spec (CommRingCat.of carrier) ⟶ S
  /-- The residue field `R ⧸ m` is of finite type over `S`. -/
  residue_locallyOfFiniteType :
    LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal carrier))) ≫ toS)

attribute [instance] CompleteLocalSAlgebra.commRing CompleteLocalSAlgebra.isLocalRing
  CompleteLocalSAlgebra.isNoetherianRing CompleteLocalSAlgebra.isCompleteLocalRing

namespace CompleteLocalSAlgebra

variable {S : Scheme.{u}}

/-- Package a Noetherian complete local ring with a structure morphism to `S` whose
residue field is of finite type over `S`. -/
def of (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsCompleteLocalRing R] (toS : Spec (CommRingCat.of R) ⟶ S)
    (h : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R))) ≫ toS)) :
    CompleteLocalSAlgebra S where
  carrier := R
  toS := toS
  residue_locallyOfFiniteType := h

/-- The packaged complete local `S`-algebra recovers the supplied carrier. -/
theorem of_carrier (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsCompleteLocalRing R] (toS : Spec (CommRingCat.of R) ⟶ S)
    (h : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R))) ≫ toS)) :
    (of R toS h).carrier = R := sorry

/-- `CompleteLocalSAlgebra.of` recovers the supplied carrier and structure morphism. -/
theorem spec (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsCompleteLocalRing R] (toS : Spec (CommRingCat.of R) ⟶ S)
    (h : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R))) ≫ toS)) :
    (of R toS h).carrier = R ∧ (of R toS h).toS = toS := sorry

/-- The `n`th maximal-adic truncation ring `R ⧸ m^{n+1}`, corresponding to the source
stage `ξ_{n+1}`. -/
abbrev truncationRing (R : CompleteLocalSAlgebra S) (n : ℕ) : CommRingCat.{u} :=
  .of (R.carrier ⧸ maximalIdeal R.carrier ^ (n + 1))

/-- Spectrum of the `n`th maximal-adic truncation, `Spec(R ⧸ m^{n+1})`. -/
def truncationSpec (R : CompleteLocalSAlgebra S) (n : ℕ) : Scheme.{u} :=
  Spec (R.truncationRing n)

/-- Canonical first-order thickening `Spec(R ⧸ m^{n+1}) ⟶ Spec(R ⧸ m^{n+2})`. -/
def truncationMap (R : CompleteLocalSAlgebra S) (n : ℕ) :
    R.truncationSpec n ⟶ R.truncationSpec (n + 1) :=
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))))

/-- Structure morphism `Spec(R ⧸ m^{n+1}) ⟶ S` of a truncation. -/
def truncationToS (R : CompleteLocalSAlgebra S) (n : ℕ) : R.truncationSpec n ⟶ S :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R.carrier ^ (n + 1)))) ≫
    R.toS

/-- Successive truncation morphisms are compatible with the structure maps to `S`. -/
theorem stageToS_comp (R : CompleteLocalSAlgebra S) (n : ℕ) :
    R.truncationMap n ≫ R.truncationToS (n + 1) = R.truncationToS n := sorry

/-- The object `Spec(R ⧸ m^{n+1}) ⟶ S` of `Over S` at stage `n`. -/
def stageOver (R : CompleteLocalSAlgebra S) (n : ℕ) : Over S :=
  Over.mk (R.truncationToS n)

/-- The morphism `Spec(R ⧸ m^{n+1}) ⟶ Spec(R ⧸ m^{n+2})` in `Over S`. -/
def stageHom (R : CompleteLocalSAlgebra S) (n : ℕ) :
    R.stageOver n ⟶ R.stageOver (n + 1) :=
  Over.homMk (R.truncationMap n) (R.stageToS_comp n)

end CompleteLocalSAlgebra

namespace GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

/-- A formal object of a category fibred in groupoids `X` over `(Sch/S)_fppf` is a
complete local `S`-algebra `R` together with objects `ξ_{n+1}` of `X` over
`Spec(R ⧸ m^{n+1})` and transition morphisms over
`Spec(R ⧸ m^{n+1}) ⟶ Spec(R ⧸ m^{n+2})`. -/
structure FormalObject (X : GroupoidsOver S) where
  /-- Complete local `S`-algebra underlying the formal object. -/
  base : CompleteLocalSAlgebra S
  /-- Stage `n` is the source object `ξ_{n+1}` over `Spec(R ⧸ m^{n+1})`. -/
  objects : ℕ → X.total
  /-- Transition `ξ_{n+1} ⟶ ξ_{n+2}` over `Spec(R ⧸ m^{n+1}) ⟶ Spec(R ⧸ m^{n+2})`. -/
  step : ∀ n, objects n ⟶ objects (n + 1)
  /-- Stage `n` lies over `Spec(R ⧸ m^{n+1}) ⟶ S`. -/
  over_obj : ∀ n, X.p.obj (objects n) = base.stageOver n
  /-- The successor morphism lies over the truncation thickening in `Over S`. -/
  over_step : ∀ n, X.p.IsHomLift (base.stageHom n) (step n)

namespace FormalObject

variable {X : GroupoidsOver S}

/-- Package a complete local `S`-algebra and a compatible forward system as a formal
object of `X`. -/
def of (base : CompleteLocalSAlgebra S) (objects : ℕ → X.total)
    (step : ∀ n, objects n ⟶ objects (n + 1))
    (over_obj : ∀ n, X.p.obj (objects n) = base.stageOver n)
    (over_step : ∀ n, X.p.IsHomLift (base.stageHom n) (step n)) :
    FormalObject X where
  base := base
  objects := objects
  step := step
  over_obj := over_obj
  over_step := over_step

/-- The packaged formal object recovers the supplied complete local `S`-algebra. -/
theorem of_base (base : CompleteLocalSAlgebra S) (objects : ℕ → X.total)
    (step : ∀ n, objects n ⟶ objects (n + 1))
    (over_obj : ∀ n, X.p.obj (objects n) = base.stageOver n)
    (over_step : ∀ n, X.p.IsHomLift (base.stageHom n) (step n)) :
    (of base objects step over_obj over_step).base = base := sorry

/-- Stagewise specification of a formal object over the truncations of its base. -/
theorem spec (ξ : FormalObject X) (n : ℕ) :
    X.p.obj (ξ.objects n) = ξ.base.stageOver n ∧
      X.p.IsHomLift (ξ.base.stageHom n) (ξ.step n) := sorry

/-- The stagewise over-object and over-step conditions are equivalent to the
bundled pair of universal conditions. -/
theorem spec_iff (ξ : FormalObject X) :
    (∀ n, X.p.obj (ξ.objects n) = ξ.base.stageOver n ∧
        X.p.IsHomLift (ξ.base.stageHom n) (ξ.step n)) ↔
      ((∀ n, X.p.obj (ξ.objects n) = ξ.base.stageOver n) ∧
        ∀ n, X.p.IsHomLift (ξ.base.stageHom n) (ξ.step n)) := sorry

/-- The source object `ξ₁`, lying over `Spec(R ⧸ m)`. -/
def stageOne (ξ : FormalObject X) : X.total :=
  ξ.objects 0

/-- The first stage of a formal object lies over `Spec(R ⧸ m) ⟶ S`. -/
theorem stageOne_over (ξ : FormalObject X) :
    X.p.obj ξ.stageOne = ξ.base.stageOver 0 := sorry

variable {Y : GroupoidsOver S}

/-- The image `F(ξ)` of a formal object along a 1-morphism of categories fibred in
groupoids: the same complete local base, with stages and transitions mapped by `F`. -/
def map (F : X ⟶ Y) (ξ : FormalObject X) : FormalObject Y where
  base := ξ.base
  objects n := (toFunctor F).obj (ξ.objects n)
  step n := (toFunctor F).map (ξ.step n)
  over_obj := sorry
  over_step := sorry

/-- Mapping a formal object along `F` preserves the complete local base. -/
theorem map_base (F : X ⟶ Y) (ξ : FormalObject X) :
    (map F ξ).base = ξ.base := sorry

/-- Stage `n` of `F(ξ)` is the image of the original stage under `F`. -/
theorem map_objects (F : X ⟶ Y) (ξ : FormalObject X) (n : ℕ) :
    (map F ξ).objects n = (toFunctor F).obj (ξ.objects n) := sorry

/-- Successor transitions of `F(ξ)` are the images of the original transitions under
`F`. -/
theorem map_step (F : X ⟶ Y) (ξ : FormalObject X) (n : ℕ) :
    (map F ξ).step n = (toFunctor F).map (ξ.step n) := sorry

/-- Unpacked meaning of `F(ξ) ≅ η`: the same complete local `S`-algebra, together with
a natural family of fibre isomorphisms over identities on the truncations. -/
def IsMappedIso (F : X ⟶ Y) (ξ : FormalObject X) (η : FormalObject Y) : Prop :=
  ξ.base = η.base ∧
    ∃ α : ∀ n, (toFunctor F).obj (ξ.objects n) ≅ η.objects n,
      (∀ n, Y.p.IsHomLift (𝟙 (η.base.stageOver n)) (α n).hom) ∧
        ∀ n, (toFunctor F).map (ξ.step n) ≫ (α (n + 1)).hom =
          (α n).hom ≫ η.step n

/-- `IsMappedIso F ξ η` is the same-base condition together with a natural family of
fibre isomorphisms `F(ξ_n) ≅ η_n`. -/
theorem isMappedIso_iff (F : X ⟶ Y) (ξ : FormalObject X) (η : FormalObject Y) :
    IsMappedIso F ξ η ↔
      ξ.base = η.base ∧
        ∃ α : ∀ n, (map F ξ).objects n ≅ η.objects n,
          (∀ n, Y.p.IsHomLift (𝟙 (η.base.stageOver n)) (α n).hom) ∧
            ∀ n, (map F ξ).step n ≫ (α (n + 1)).hom = (α n).hom ≫ η.step n :=
  sorry

end FormalObject

end GroupoidsOver

end AlgebraicGeometry

