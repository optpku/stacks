module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap71.Lemma_71_6_12_Pullback

/-!
# Lifts through U-admissible blowups

A morphism of algebraic spaces that lands in an open `U ⊂ X` lifts uniquely
along a `U`-admissible blowup `b : X' ⟶ X`. The lift is independent of the
choice of finitely presented center disjoint from `U`, and induces a morphism
into the blown-up fibre product.

Chap71 `IsAdmissibleBlowupCenter` and Chap66 open-lift currently rebuild the
broken `Lemma_66_4_2_Comparison` (private `Scheme.FieldValuedPoint` constructor).
This module reconstructs those compiling owners from `OpenSubspace`, `Points`,
`IsEffectiveCartierDivisor`, and fibre products.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inclusion of an open subspace is an open immersion. -/
instance OpenSubspace.instIsOpenImmersion {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : OpenSubspace X) : IsOpenImmersion U.ι :=
  U.isOpenImmersion

/-- The underlying set of points of an open subspace, as the image of `|U| → |X|`. -/
def OpenSubspace.pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : OpenSubspace X) : Set (Points X) :=
  Set.range (Points.map U.ι)

/-- `OpenSubspace.pointsSet U` is the range of `Points.map U.ι`. -/
theorem OpenSubspace.pointsSet_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : OpenSubspace X) :
    U.pointsSet = Set.range (Points.map U.ι) :=
  sorry

/-- A point of `|X|` lies in `U.pointsSet` if and only if it is the image of a
point of `|U|`. -/
theorem OpenSubspace.mem_pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : OpenSubspace X) {x : Points X} :
    x ∈ U.pointsSet ↔ ∃ y : Points U.X, Points.map U.ι y = x :=
  sorry

/-- The underlying set of points of a closed subspace, as the image of `|Z| → |X|`. -/
def ClosedSubspace.pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) : Set (Points X) :=
  Set.range (Points.map Z.ι)

/-- `ClosedSubspace.pointsSet Z` is the range of `Points.map Z.ι`. -/
theorem ClosedSubspace.pointsSet_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) :
    Z.pointsSet = Set.range (Points.map Z.ι) :=
  sorry

/-- A point of `|X|` lies in `Z.pointsSet` if and only if it is the image of a
point of `|Z|`. -/
theorem ClosedSubspace.mem_pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) {x : Points X} :
    x ∈ Z.pointsSet ↔ ∃ y : Points Z.X, Points.map Z.ι y = x :=
  sorry

namespace IsOpenImmersion

/-- A morphism of algebraic spaces factors uniquely through an open immersion if
and only if the induced map on points lands in the image of that immersion. -/
theorem existsUnique_lift_iff_range_subset {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (i : Z ⟶ X) [IsOpenImmersion i] (f : Y ⟶ X) :
    (∃! g : Y ⟶ Z, g ≫ i = f) ↔
      Set.range (Points.map f) ⊆ Set.range (Points.map i) :=
  sorry

end IsOpenImmersion

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

/-- An admissible center is of finite presentation over the base algebraic space.
This cannot be a global `FinitePresentation` instance: `U` and `f` are not
determined by `Z.ι`. -/
theorem IsAdmissibleBlowupCenter.finitePresentation {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} {U : OpenSubspace X} {f : X' ⟶ X} {Z : ClosedSubspace X}
    [h : IsAdmissibleBlowupCenter U f Z] : FinitePresentation Z.ι :=
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

/-- A `U`-admissible blowup is an isomorphism over `U`. The center is an explicit
parameter, so this cannot be a global `IsIso` instance. -/
theorem isIso_pullbackFst_of_isAdmissibleBlowupCenter
    {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (U : OpenSubspace X) (b : X' ⟶ X) (center : ClosedSubspace X)
    [IsAdmissibleBlowupCenter U b center] :
    IsIso (pullback.fst U.ι b) :=
  sorry

/-- The inverse of `pullback.fst U.ι b` supplied by an isomorphism over `U`. -/
noncomputable def admissibleOpenPullbackInv {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    {U : OpenSubspace X} {b : X' ⟶ X} (hiso : IsIso (pullback.fst U.ι b)) :
    U.X ⟶ pullback U.ι b :=
  @inv (AlgebraicSpace S) _ _ _ (pullback.fst U.ι b) hiso

/-- The inverse of the first projection recomposes to the identity of `U`. -/
theorem admissibleOpenPullbackInv_fac {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    {U : OpenSubspace X} {b : X' ⟶ X} (hiso : IsIso (pullback.fst U.ι b)) :
    admissibleOpenPullbackInv hiso ≫ pullback.fst U.ι b = 𝟙 U.X :=
  sorry

/-- The canonical lift of a morphism factoring through `U` along a morphism that is
an isomorphism over `U`. -/
noncomputable def liftAdmissible {S : Scheme.{u}} {W X X' : AlgebraicSpace S}
    (U : OpenSubspace X) (b : X' ⟶ X)
    (hU : W ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b)) : W ⟶ X' :=
  hU ≫ admissibleOpenPullbackInv hiso ≫ pullback.snd U.ι b

/-- The admissible lift is the composite of the factorization through `U`, the
inverse of `pullback.fst U.ι b`, and the second projection. -/
theorem liftAdmissible_eq {S : Scheme.{u}} {W X X' : AlgebraicSpace S}
    (U : OpenSubspace X) (b : X' ⟶ X)
    (hU : W ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b)) :
    liftAdmissible U b hU hiso =
      hU ≫ admissibleOpenPullbackInv hiso ≫ pullback.snd U.ι b :=
  sorry

/-- The admissible lift composes with `b` to the original morphism through `U`. -/
theorem liftAdmissible_fac {S : Scheme.{u}} {W X X' : AlgebraicSpace S}
    (U : OpenSubspace X) (b : X' ⟶ X)
    (hU : W ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b))
    {h : W ⟶ X} (hqU : hU ≫ U.ι = h) :
    liftAdmissible U b hU hiso ≫ b = h :=
  sorry

/-- The two legs defining the lifted morphism to `X' ×_B Y` commute over `B`. -/
theorem liftAdmissiblePullback_condition {S : Scheme.{u}}
    {B X Y V X' : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B)
    (q : V ⟶ pullback f g) (U : OpenSubspace X) (b : X' ⟶ X)
    (qU : V ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b))
    (hqU : qU ≫ U.ι = q ≫ pullback.fst f g) :
    liftAdmissible U b qU hiso ≫ (b ≫ f) = (q ≫ pullback.snd f g) ≫ g :=
  sorry

/-- The morphism `V ⟶ X' ×_B Y` obtained by lifting the first projection of `q`
along a morphism that is an isomorphism over `U`. -/
noncomputable def liftAdmissiblePullback {S : Scheme.{u}}
    {B X Y V X' : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B)
    (q : V ⟶ pullback f g) (U : OpenSubspace X) (b : X' ⟶ X)
    (qU : V ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b))
    (hqU : qU ≫ U.ι = q ≫ pullback.fst f g) :
    V ⟶ pullback (b ≫ f) g :=
  pullback.lift
    (liftAdmissible U b qU hiso)
    (q ≫ pullback.snd f g)
    (liftAdmissiblePullback_condition f g q U b qU hiso hqU)

/-- The first projection of the lifted pullback morphism is the admissible lift. -/
theorem liftAdmissiblePullback_fst {S : Scheme.{u}}
    {B X Y V X' : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B)
    (q : V ⟶ pullback f g) (U : OpenSubspace X) (b : X' ⟶ X)
    (qU : V ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b))
    (hqU : qU ≫ U.ι = q ≫ pullback.fst f g) :
    liftAdmissiblePullback f g q U b qU hiso hqU ≫ pullback.fst (b ≫ f) g =
      liftAdmissible U b qU hiso :=
  sorry

/-- The second projection of the lifted pullback morphism agrees with that of `q`. -/
theorem liftAdmissiblePullback_snd {S : Scheme.{u}}
    {B X Y V X' : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B)
    (q : V ⟶ pullback f g) (U : OpenSubspace X) (b : X' ⟶ X)
    (qU : V ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b))
    (hqU : qU ≫ U.ι = q ≫ pullback.fst f g) :
    liftAdmissiblePullback f g q U b qU hiso hqU ≫ pullback.snd (b ≫ f) g =
      q ≫ pullback.snd f g :=
  sorry

/-- The lifted morphism to `X' ×_B Y` is the unique map induced by the admissible
lift of the first projection and the original second projection. -/
theorem liftAdmissiblePullback_spec {S : Scheme.{u}}
    {B X Y V X' : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B)
    (q : V ⟶ pullback f g) (U : OpenSubspace X) (b : X' ⟶ X)
    (qU : V ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b))
    (hqU : qU ≫ U.ι = q ≫ pullback.fst f g) :
    liftAdmissiblePullback f g q U b qU hiso hqU ≫ pullback.fst (b ≫ f) g =
        liftAdmissible U b qU hiso ∧
      liftAdmissiblePullback f g q U b qU hiso hqU ≫ pullback.snd (b ≫ f) g =
        q ≫ pullback.snd f g :=
  sorry

/-- Quasi-compactness is preserved by the canonical lift to the blown-up fibre
product. -/
instance instQuasiCompact_liftAdmissiblePullback {S : Scheme.{u}}
    {B X Y V X' : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B)
    (q : V ⟶ pullback f g) [QuasiCompact q]
    (U : OpenSubspace X) (b : X' ⟶ X)
    (qU : V ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b))
    (hqU : qU ≫ U.ι = q ≫ pullback.fst f g) :
    QuasiCompact (liftAdmissiblePullback f g q U b qU hiso hqU) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
