/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_12_3_Pullback
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_13_1_Correspondence
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation

/-!
# Admissible blowups of algebraic spaces

A morphism of algebraic spaces is a blowup in a closed subspace when it is
terminal among morphisms making the inverse image an effective Cartier
divisor. It is `U`-admissible when the center is finitely presented and
disjoint from the open subspace `U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inclusion of an open subspace is an open immersion. -/
instance OpenSubspace.instIsOpenImmersion {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : OpenSubspace X) : IsOpenImmersion U.ι :=
  U.isOpenImmersion

/-- The inclusion of a closed subspace is a closed immersion. -/
instance ClosedSubspace.instIsClosedImmersion {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) : IsClosedImmersion Z.ι :=
  Z.isClosedImmersion

/-- The intersection `U ∩ V`, viewed as an open subspace of `V`, is the pullback of
`U.ι` along `V.ι`. -/
def OpenSubspace.preimage {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U V : OpenSubspace X) : OpenSubspace V.X where
  X := pullback U.ι V.ι
  ι := pullback.snd U.ι V.ι
  isOpenImmersion := IsOpenImmersion.pullback_snd U.isOpenImmersion V.ι

/-- The underlying space of `U.preimage V` is the fibre product of the inclusions. -/
theorem OpenSubspace.preimage_X {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U V : OpenSubspace X) : (U.preimage V).X = pullback U.ι V.ι :=
  sorry

/-- The inclusion of `U.preimage V` into `V` is the second projection of the fibre
product of the inclusions. -/
theorem OpenSubspace.preimage_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U V : OpenSubspace X) : (U.preimage V).ι = pullback.snd U.ι V.ι :=
  sorry

/-- `U.preimage V` is the fibre product of the inclusions, included into `V` by the
second projection, and that inclusion is an open immersion. -/
theorem OpenSubspace.preimage_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U V : OpenSubspace X) :
    (U.preimage V).X = pullback U.ι V.ι ∧
      (U.preimage V).ι = pullback.snd U.ι V.ι ∧
        IsOpenImmersion (U.preimage V).ι :=
  sorry

/-- A closed immersion of algebraic spaces is an effective Cartier divisor when its
associated ideal sheaf is invertible, i.e. finite locally free of rank one. -/
class IsEffectiveCartierDivisor {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) : Prop extends IsClosedImmersion i where
  /-- The associated ideal sheaf is finite locally free of rank one. -/
  isFiniteLocallyFreeOfRank_one_idealSheaf :
    SheafOfModules.IsFiniteLocallyFreeOfRank 1 (Hom.idealSheaf i)

/-- An effective Cartier divisor is a closed immersion whose associated ideal sheaf is
finite locally free of rank one. -/
theorem isEffectiveCartierDivisor_iff {S : Scheme.{u}} {D X : AlgebraicSpace S}
    (i : D ⟶ X) :
    IsEffectiveCartierDivisor i ↔
      IsClosedImmersion i ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank 1 (Hom.idealSheaf i) :=
  sorry

/-- The empty closed subspace, cut out by the unit ideal, is an effective Cartier
divisor. -/
instance instIsEffectiveCartierDivisor_top {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsEffectiveCartierDivisor
      (ClosedSubspace.ofQuasiCoherentIdeal (⊤ : IdealSubobject X)).ι :=
  sorry

/-- A morphism `f : X' ⟶ X` is a blowup of `X` in the closed subspace `Z` when the
inverse image of `Z` is an effective Cartier divisor and `f` is terminal among
morphisms to `X` with that property. -/
class IsBlowup {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (f : X' ⟶ X) (Z : ClosedSubspace X) : Prop where
  /-- The inverse image of the center is an effective Cartier divisor. -/
  inverseImage_isEffectiveCartier : IsEffectiveCartierDivisor (pullback.snd Z.ι f)
  /-- The blowup is terminal among morphisms to `X` whose inverse image of `Z` is an
  effective Cartier divisor. -/
  lift_unique {Y : AlgebraicSpace S} (g : Y ⟶ X)
      (hg : IsEffectiveCartierDivisor (pullback.snd Z.ι g)) :
    ExistsUnique fun h : Y ⟶ X' ↦ h ≫ f = g

/-- The inverse image of the center of a blowup is an effective Cartier divisor. -/
instance instIsEffectiveCartierDivisor_inverseImage
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} {f : X' ⟶ X} {Z : ClosedSubspace X}
    [h : IsBlowup f Z] : IsEffectiveCartierDivisor (pullback.snd Z.ι f) :=
  h.inverseImage_isEffectiveCartier

/-- A blowup is uniquely characterized by the universal property among morphisms making
the inverse image of the center an effective Cartier divisor. -/
theorem IsBlowup.existsUnique_lift {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    {f : X' ⟶ X} {Z : ClosedSubspace X} [h : IsBlowup f Z] {Y : AlgebraicSpace S}
    (g : Y ⟶ X) (hg : IsEffectiveCartierDivisor (pullback.snd Z.ι g)) :
    ExistsUnique fun h' : Y ⟶ X' ↦ h' ≫ f = g :=
  sorry

/-- A morphism is a blowup in `Z` exactly when the inverse image of `Z` is an
effective Cartier divisor and the morphism is terminal among such maps. -/
theorem isBlowup_iff {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (f : X' ⟶ X) (Z : ClosedSubspace X) :
    IsBlowup f Z ↔
      IsEffectiveCartierDivisor (pullback.snd Z.ι f) ∧
        ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X),
          IsEffectiveCartierDivisor (pullback.snd Z.ι g) →
            ExistsUnique fun h : Y ⟶ X' ↦ h ≫ f = g :=
  sorry

/-- The identity of `X` is the blowup of `X` in an effective Cartier divisor. -/
instance instIsBlowup_id_of_isEffectiveCartierDivisor
    {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    [IsEffectiveCartierDivisor Z.ι] : IsBlowup (𝟙 X) Z :=
  sorry

/-- A center for a `U`-admissible blowup is a finitely presented closed subspace of
`X` disjoint from `U`, together with a blowup structure on the morphism. -/
class IsAdmissibleBlowupCenter {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (U : OpenSubspace X) (f : X' ⟶ X) (Z : ClosedSubspace X) : Prop
    extends IsBlowup f Z where
  /-- The closed-subspace inclusion of the center is of finite presentation. -/
  finitePresentation_ι : FinitePresentation Z.ι
  /-- The center is disjoint from the open subspace `U`. -/
  disjoint_pointsSet : Disjoint Z.pointsSet U.pointsSet

/-- An admissible center is of finite presentation over the base algebraic space. -/
theorem IsAdmissibleBlowupCenter.finitePresentation {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} {U : OpenSubspace X} {f : X' ⟶ X} {Z : ClosedSubspace X}
    [h : IsAdmissibleBlowupCenter U f Z] : FinitePresentation Z.ι :=
  sorry

/-- An admissible center exhibits the given morphism as a blowup in that center. -/
theorem IsAdmissibleBlowupCenter.isBlowup {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} {U : OpenSubspace X} {f : X' ⟶ X} {Z : ClosedSubspace X}
    [h : IsAdmissibleBlowupCenter U f Z] : IsBlowup f Z :=
  sorry

/-- A center is admissible exactly when it is a finitely presented blowup center
disjoint from the chosen open subspace. -/
theorem isAdmissibleBlowupCenter_iff {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (U : OpenSubspace X) (f : X' ⟶ X) (Z : ClosedSubspace X) :
    IsAdmissibleBlowupCenter U f Z ↔
      IsBlowup f Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet :=
  sorry

/-- The identity of `X` is a `U`-admissible blowup with empty center, cut out by the
unit ideal. -/
instance instIsAdmissibleBlowupCenter_id {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : OpenSubspace X) :
    IsAdmissibleBlowupCenter U (𝟙 X)
      (ClosedSubspace.ofQuasiCoherentIdeal (⊤ : IdealSubobject X)) :=
  sorry

/-- A morphism `f : X' ⟶ X` is a `U`-admissible blowup when it is the blowup in a
finitely presented closed subspace disjoint from `U`. -/
def IsAdmissibleBlowup {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (U : OpenSubspace X) (f : X' ⟶ X) : Prop :=
  ∃ Z : ClosedSubspace X, IsAdmissibleBlowupCenter U f Z

/-- A `U`-admissible blowup is obtained from any admissible center. -/
theorem IsAdmissibleBlowup.mk {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    {U : OpenSubspace X} {f : X' ⟶ X} (Z : ClosedSubspace X)
    [IsAdmissibleBlowupCenter U f Z] : IsAdmissibleBlowup U f :=
  sorry

/-- An admissible blowup comes equipped with an admissible center. -/
theorem IsAdmissibleBlowup.exists_center {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    {U : OpenSubspace X} {f : X' ⟶ X} (hf : IsAdmissibleBlowup U f) :
    ∃ Z : ClosedSubspace X, IsAdmissibleBlowupCenter U f Z :=
  sorry

/-- A `U`-admissible blowup admits a finitely presented center disjoint from `U` for
which the morphism is a blowup. -/
theorem IsAdmissibleBlowup.exists_center_spec {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} {U : OpenSubspace X} {f : X' ⟶ X}
    (hf : IsAdmissibleBlowup U f) :
    ∃ Z : ClosedSubspace X,
      IsBlowup f Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet :=
  sorry

/-- A morphism is `U`-admissible exactly when it admits a finitely presented center
disjoint from `U` for which it is a blowup. -/
theorem isAdmissibleBlowup_iff {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (U : OpenSubspace X) (f : X' ⟶ X) :
    IsAdmissibleBlowup U f ↔
      ∃ Z : ClosedSubspace X,
        IsBlowup f Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet :=
  sorry

/-- The identity of `X` is a `U`-admissible blowup. -/
theorem IsAdmissibleBlowup.id {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : OpenSubspace X) : IsAdmissibleBlowup U (𝟙 X) :=
  sorry

/-- An admissible blowup of a quasi-compact open subspace of a quasi-compact
quasi-separated algebraic space extends to an admissible blowup of the whole space
whose center avoids a prescribed quasi-compact open, with the original blowup
recovered by restriction. -/
theorem exists_isAdmissibleBlowup_restrict_iso_of_isAdmissibleBlowup_inter
    {S : Scheme.{u}} {X V' : AlgebraicSpace S} [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (U V : OpenSubspace X)
    [QuasiCompact U.ι] [QuasiCompact V.ι] (b : V' ⟶ V.X)
    (hb : IsAdmissibleBlowup (U.preimage V) b) :
    ∃ (X' : AlgebraicSpace S) (π : X' ⟶ X),
      IsAdmissibleBlowup U π ∧ Nonempty (Over.mk (pullback.snd π V.ι) ≅ Over.mk b) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
