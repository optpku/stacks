/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.MotivicRealization
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical
public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.IsWeil

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace WeilCohomology

namespace SchemeClassicalTheory

/-- A first-class presentation of data (D0)--(D3) satisfying axioms (A)--(C). -/
structure Object
    (k : Type u) [Field k] (F : Type v) [Field F] [CharZero F] where
  /-- The chosen one-dimensional Tate line. -/
  TateLine : ModuleCat.{max (u + 1) v} F
  /-- A presentation of the category of smooth projective schemes. -/
  V : Cat.{max (u + 1) v, max (u + 1) v}
  /-- The dimension of each represented scheme. -/
  dimension : V → ℕ
  /-- The chosen product of represented schemes. -/
  product : V → V → V
  /-- The first projection from the chosen product. -/
  fst : ∀ X Y, product X Y ⟶ X
  /-- The second projection from the chosen product. -/
  snd : ∀ X Y, product X Y ⟶ Y
  /-- The chosen point object. -/
  point : V
  /-- The total cohomology algebra of each represented scheme. -/
  H : V → AlgCat.{max (u + 1) v} F
  /-- The Chow ring of each represented scheme. -/
  CH : V → CommRingCat.{max (u + 1) v}
  /-- The cohomological and Tate bigrading. -/
  Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X)
  /-- The codimension grading on Chow groups. -/
  CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)
  /-- The total cohomology algebra is the direct sum of its bigraded pieces. -/
  hHgrade : ∀ X, GradedAlgebra (Hgrade X)
  /-- The Chow ring is the direct sum of its graded pieces. -/
  hCHgrade : ∀ X, GradedAlgebra (CHgrade X)
  /-- Pullback on graded Chow groups. -/
  cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X
  /-- Pushforward on total Chow groups. -/
  cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y
  /-- The classical Weil theory carried by these data. -/
  theory : @SchemeClassicalTheory k _ F _ _ TateLine _ _ V _
    dimension product fst snd point (fun X ↦ H X) (fun X ↦ CH X) _ _ _
    Hgrade CHgrade hHgrade hCHgrade cyclePullback cyclePushforward

namespace Object

/-- Assemble a classical-theory object from its explicit carriers, operations,
gradings, and axioms. -/
def of
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    (TateLine : ModuleCat.{max (u + 1) v} F)
    (V : Cat.{max (u + 1) v, max (u + 1) v})
    (dimension : V → ℕ) (product : V → V → V)
    (fst : ∀ X Y, product X Y ⟶ X) (snd : ∀ X Y, product X Y ⟶ Y)
    (point : V) (H : V → AlgCat.{max (u + 1) v} F)
    (CH : V → CommRingCat.{max (u + 1) v})
    (Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X))
    (CHgrade : ∀ X, ℤ → Submodule ℤ (CH X))
    (hHgrade : ∀ X, GradedAlgebra (Hgrade X))
    (hCHgrade : ∀ X, GradedAlgebra (CHgrade X))
    (cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X)
    (cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y)
    (theory : @SchemeClassicalTheory k _ F _ _ TateLine _ _ V _
      dimension product fst snd point (fun X ↦ H X) (fun X ↦ CH X) _ _ _
      Hgrade CHgrade hHgrade hCHgrade cyclePullback cyclePushforward) :
    Object k F where
  TateLine := TateLine
  V := V
  dimension := dimension
  product := product
  fst := fst
  snd := snd
  point := point
  H := H
  CH := CH
  Hgrade := Hgrade
  CHgrade := CHgrade
  hHgrade := hHgrade
  hCHgrade := hCHgrade
  cyclePullback := cyclePullback
  cyclePushforward := cyclePushforward
  theory := theory

/-- The theory projection of `Object.of` is the supplied classical Weil theory. -/
theorem of_theory
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    (TateLine : ModuleCat.{max (u + 1) v} F)
    (V : Cat.{max (u + 1) v, max (u + 1) v})
    (dimension : V → ℕ) (product : V → V → V)
    (fst : ∀ X Y, product X Y ⟶ X) (snd : ∀ X Y, product X Y ⟶ Y)
    (point : V) (H : V → AlgCat.{max (u + 1) v} F)
    (CH : V → CommRingCat.{max (u + 1) v})
    (Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X))
    (CHgrade : ∀ X, ℤ → Submodule ℤ (CH X))
    (hHgrade : ∀ X, GradedAlgebra (Hgrade X))
    (hCHgrade : ∀ X, GradedAlgebra (CHgrade X))
    (cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X)
    (cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y)
    (theory : @SchemeClassicalTheory k _ F _ _ TateLine _ _ V _
      dimension product fst snd point (fun X ↦ H X) (fun X ↦ CH X) _ _ _
      Hgrade CHgrade hHgrade hCHgrade cyclePullback cyclePushforward) :
    (of TateLine V dimension product fst snd point H CH Hgrade CHgrade
      hHgrade hCHgrade cyclePullback cyclePushforward theory).theory = theory := rfl

/-- A bundled classical-theory object is Weil when its stored theory is Weil
with the grading laws carried by the bundle. -/
def IsWeil {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    (T : Object k F) : Prop :=
  @SchemeClassicalTheory.IsWeil k _ F _ _ T.TateLine _ _ T.V _
    T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
    _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
    T.cyclePushforward T.theory

/-- The bundled classical-theory Weil condition is the Weil condition on the
stored theory with the stored grading laws. -/
theorem isWeil_iff {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    (T : Object k F) :
    T.IsWeil ↔
      @SchemeClassicalTheory.IsWeil k _ F _ _ T.TateLine _ _ T.V _
        T.dimension T.product T.fst T.snd T.point (fun X ↦ T.H X) (fun X ↦ T.CH X)
        _ _ _ T.Hgrade T.CHgrade T.hHgrade T.hCHgrade T.cyclePullback
        T.cyclePushforward T.theory := sorry

end Object

end SchemeClassicalTheory

namespace MotivicRealization

/-- A ℚ-linear strong monoidal realization of Chow motives, compatible with the
Koszul symmetry and concentrated on the Tate motive in degree `-2`. -/
structure Admissible
    (k : Type u) [Field k] (F : Type v) [Field F] [CharZero F] where
  /-- The underlying realization functor. -/
  functor : ChowMotive k
      (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k) ⥤
    GradedObject ℤ (ModuleCat F)
  /-- The chosen ℚ-linear structure. -/
  linear : functor.Linear ℚ
  /-- The chosen strong monoidal structure. -/
  monoidal : functor.Monoidal
  /-- The chosen monoidal structure carries motivic symmetry to Koszul symmetry. -/
  koszul : @IsKoszulBraided k _ F _ functor monoidal
  /-- The Tate motive has no component outside degree `-2`. -/
  tate : ∀ i : ℤ, i ≠ -2 →
    IsZero ((functor.obj (ChowMotive.tateTwist (SchemeOverField.point k) 1)) i)

namespace Admissible

/-- Assemble an admissible realization from its functor and chosen structures. -/
def of
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    (G : ChowMotive k
        (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F))
    (linear : G.Linear ℚ) (monoidal : G.Monoidal)
    (koszul : @IsKoszulBraided k _ F _ G monoidal)
    (tate : ∀ i : ℤ, i ≠ -2 →
      IsZero ((G.obj (ChowMotive.tateTwist (SchemeOverField.point k) 1)) i)) :
    Admissible k F where
  functor := G
  linear := linear
  monoidal := monoidal
  koszul := koszul
  tate := tate

/-- The functor projection of `Admissible.of` is the supplied realization functor. -/
theorem of_functor
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    (G : ChowMotive k
        (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F))
    (linear : G.Linear ℚ) (monoidal : G.Monoidal)
    (koszul : @IsKoszulBraided k _ F _ G monoidal)
    (tate : ∀ i : ℤ, i ≠ -2 →
      IsZero ((G.obj (ChowMotive.tateTwist (SchemeOverField.point k) 1)) i)) :
    (of G linear monoidal koszul tate).functor = G := rfl

/-- The Tate-vanishing projection of `Admissible.of` is the supplied condition. -/
theorem of_tate
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    (G : ChowMotive k
        (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F))
    (linear : G.Linear ℚ) (monoidal : G.Monoidal)
    (koszul : @IsKoszulBraided k _ F _ G monoidal)
    (tate : ∀ i : ℤ, i ≠ -2 →
      IsZero ((G.obj (ChowMotive.tateTwist (SchemeOverField.point k) 1)) i)) :
    (of G linear monoidal koszul tate).tate = tate := rfl

/-- An admissible motivic realization is Weil when pullback from any smooth
projective representative of the spectrum of global sections is bijective in
degree zero. -/
def IsWeil {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    (G : Admissible k F) : Prop :=
  ∀ (X K : Correspondence.Category k) (s : X.scheme ⟶ K.scheme)
    (eK : K.scheme ≅ Over.mk (Scheme.Hom.globalSectionsSpecMap X.scheme.hom)),
    (s ≫ eK.hom).left = Scheme.toSpecΓ X.scheme.left →
      Function.Bijective ((MotivicRealization.pullback G.functor s) 0)

/-- The quantified degree-zero global-sections characterization of a Weil
admissible motivic realization. -/
theorem isWeil_iff {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    (G : Admissible k F) :
    G.IsWeil ↔
      ∀ (X K : Correspondence.Category k) (s : X.scheme ⟶ K.scheme)
        (eK : K.scheme ≅ Over.mk (Scheme.Hom.globalSectionsSpecMap X.scheme.hom)),
        (s ≫ eK.hom).left = Scheme.toSpecΓ X.scheme.left →
          Function.Bijective ((MotivicRealization.pullback G.functor s) 0) := sorry

namespace IsWeil

/-- A Weil admissible realization has bijective degree-zero pullback from a
smooth projective representative of the spectrum of global sections. -/
theorem globalSectionsPullback_bijective
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {G : Admissible k F} (hG : G.IsWeil)
    {X K : Correspondence.Category k} (s : X.scheme ⟶ K.scheme)
    (eK : K.scheme ≅ Over.mk (Scheme.Hom.globalSectionsSpecMap X.scheme.hom))
    (hs : (s ≫ eK.hom).left = Scheme.toSpecΓ X.scheme.left) :
    Function.Bijective ((MotivicRealization.pullback G.functor s) 0) := sorry

end IsWeil

end Admissible

end MotivicRealization

/-- For a field `k` and a characteristic-zero field `F`, there is a one-to-one
correspondence between data (D0)--(D3) satisfying (A)--(C) and ℚ-linear strong
monoidal, Koszul-symmetric motivic realizations whose Tate motive is zero
outside degree `-2`. -/
theorem classicalTheoryCorrespondence
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F] :
    Nonempty (SchemeClassicalTheory.Object k F ≃ MotivicRealization.Admissible k F) := sorry

/-- For a field `k` and a characteristic-zero field `F`, there is a one-to-one
correspondence between Weil classical theories and Weil admissible motivic
realizations, identifying the two Weil predicates. -/
theorem weilTheoryCorrespondence
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F] :
    ∃ e : SchemeClassicalTheory.Object k F ≃ MotivicRealization.Admissible k F,
      ∀ T, T.IsWeil ↔ (e T).IsWeil := sorry

end WeilCohomology
