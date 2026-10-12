/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import ReasLib.AlgebraicGeometry.ChowGroup.Localization
public import stacks_project.Chap42.Remark_42_27_2
public import stacks_project.Chap42.Remark_42_27_3_FirstHigher

/-!
# Localization of first higher Chow groups

This file defines the degreewise primed closed pushforward, open pullback, and extend-by-zero
section associated to an open subscheme and its reduced closed complement, the induced morphisms
of primed Milnor complexes, and the resulting maps on first higher Chow groups.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Function

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

variable {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]

/-- The reduced closed complement of an open subscheme of `X`. -/
abbrev reducedClosedComplement (U : X.Opens) : Scheme.{u} :=
  (Scheme.ClosedSubschemeStructure.reduced U.compl).subscheme

/-- The closed immersion of the reduced closed complement of an open subscheme. -/
abbrev reducedClosedComplementι (U : X.Opens) : reducedClosedComplement U ⟶ X :=
  (Scheme.ClosedSubschemeStructure.reduced U.compl).ι

/-- Relative dimension is preserved by the open immersion of an open subscheme. -/
theorem relativeDimensionFunction_open (U : X.Opens) (u : U.toScheme) :
    p.relativeDimensionFunction δ (U.ι u) = (U.ι ≫ p).relativeDimensionFunction δ u := sorry

/-- Relative dimension is preserved by the closed immersion of the reduced complement. -/
theorem relativeDimensionFunction_closed (U : X.Opens) (y : reducedClosedComplement U) :
    p.relativeDimensionFunction δ (reducedClosedComplementι U y) =
      (reducedClosedComplementι U ≫ p).relativeDimensionFunction δ y := sorry

/-- A closed immersion induces a bijection of residue fields at every point. -/
theorem residueFieldMap_bijective_of_isClosedImmersion {Y Z : Scheme.{u}}
    (f : Y ⟶ Z) [IsClosedImmersion f] (y : Y) :
    Function.Bijective (f.residueFieldMap y).hom := sorry

/-- The residue-field map of an open immersion, inverted so as to send `κ(u)` into `κ(ι u)`. -/
def openResidueFieldHom (U : X.Opens) (u : U.toScheme) :
    U.toScheme.residueField u →+* X.residueField (U.ι u) :=
  (inv (U.ι.residueFieldMap u)).hom

/-- The residue-field map of the reduced closed complement, inverted so as to send `κ(y)`
into `κ(ι y)`. -/
def closedResidueFieldHom (U : X.Opens) (y : reducedClosedComplement U) :
    (reducedClosedComplement U).residueField y →+*
      X.residueField (reducedClosedComplementι U y) where
  toFun := Function.invFun ((reducedClosedComplementι U).residueFieldMap y).hom
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Transport of a Milnor K-class along the open immersion of `U`, from `κ(u)` to `κ(ι u)`. -/
def mapAlongOpen (U : X.Opens) (n : ℕ) (u : U.toScheme) (x : X) (h : U.ι u = x) :
    MilnorK.Group n (U.toScheme.residueField u) →+ MilnorK.Group n (X.residueField x) :=
  MilnorK.mapGroup ((X.residueFieldCongr h).hom.hom.comp (openResidueFieldHom U u)) n

/-- Transport of a Milnor K-class along the reduced closed complement, from `κ(y)` to `κ(ι y)`. -/
def mapAlongClosed (U : X.Opens) (n : ℕ) (y : reducedClosedComplement U) (x : X)
    (h : reducedClosedComplementι U y = x) :
    MilnorK.Group n ((reducedClosedComplement U).residueField y) →+
      MilnorK.Group n (X.residueField x) :=
  MilnorK.mapGroup ((X.residueFieldCongr h).hom.hom.comp (closedResidueFieldHom U y)) n

/-- Restriction of a Milnor K-class along an open immersion, from `κ(ι u)` to `κ(u)`. -/
def mapRestrictOpen (U : X.Opens) (n : ℕ) (u : U.toScheme) :
    MilnorK.Group n (X.residueField (U.ι u)) →+
      MilnorK.Group n (U.toScheme.residueField u) :=
  MilnorK.mapGroup (U.ι.residueFieldMap u).hom n

/-- Restriction of a Milnor K-class along the reduced closed complement, from `κ(ι y)` to `κ(y)`. -/
def mapRestrictClosed (U : X.Opens) (n : ℕ) (y : reducedClosedComplement U) :
    MilnorK.Group n (X.residueField (reducedClosedComplementι U y)) →+
      MilnorK.Group n ((reducedClosedComplement U).residueField y) :=
  MilnorK.mapGroup ((reducedClosedComplementι U).residueFieldMap y).hom n

end AlgebraicGeometry.ChowGroup

namespace AlgebraicGeometry.ChowGroup.Pointwise

open AlgebraicGeometry.ChowGroup

variable {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
variable (U : X.Opens) (k : ℤ)

open Classical in
/-- Underlying coefficients of primed degree-two closed pushforward. -/
def degreeTwoClosedPushforward_toFun (n : degreeTwoLocallyFinite
    ((reducedClosedComplementι U ≫ p).relativeDimensionFunction δ) (k + 2)) :
    degreeTwoCoefficients (p.relativeDimensionFunction δ) (k + 2) :=
  fun x ↦ ∑ᶠ y : {y : reducedClosedComplement U //
      (reducedClosedComplementι U ≫ p).relativeDimensionFunction δ y = k + 2},
    if h : reducedClosedComplementι U y.1 = x.1 then
      mapAlongClosed U 2 y.1 x.1 h (n.1 y)
    else
      0

/-- Closed pushforward of primed degree-two families from the reduced complement. -/
def degreeTwoClosedPushforward :
    degreeTwoLocallyFinite
        ((reducedClosedComplementι U ≫ p).relativeDimensionFunction δ) (k + 2) →+
      degreeTwoLocallyFinite (p.relativeDimensionFunction δ) (k + 2) where
  toFun n := ⟨degreeTwoClosedPushforward_toFun p δ U k n, sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- Underlying coefficients of primed degree-two open pullback. -/
def degreeTwoOpenPullback_toFun
    (n : degreeTwoLocallyFinite (p.relativeDimensionFunction δ) (k + 2)) :
    degreeTwoCoefficients ((U.ι ≫ p).relativeDimensionFunction δ) (k + 2) :=
  fun u ↦ mapRestrictOpen U 2 u.1
    (n.1 ⟨U.ι u.1, (relativeDimensionFunction_open p δ U u.1).trans u.2⟩)

/-- Open pullback of primed degree-two families to an open subscheme. -/
def degreeTwoOpenPullback :
    degreeTwoLocallyFinite (p.relativeDimensionFunction δ) (k + 2) →+
      degreeTwoLocallyFinite ((U.ι ≫ p).relativeDimensionFunction δ) (k + 2) where
  toFun n := ⟨degreeTwoOpenPullback_toFun p δ U k n, sorry⟩
  map_zero' := sorry
  map_add' := sorry

open Classical in
/-- Underlying coefficients of primed degree-two extend-by-zero. -/
def degreeTwoExtendByZero_toFun (n : degreeTwoLocallyFinite
    ((U.ι ≫ p).relativeDimensionFunction δ) (k + 2)) :
    degreeTwoCoefficients (p.relativeDimensionFunction δ) (k + 2) :=
  fun x ↦ ∑ᶠ u : {u : U.toScheme // (U.ι ≫ p).relativeDimensionFunction δ u = k + 2},
    if h : U.ι u.1 = x.1 then mapAlongOpen U 2 u.1 x.1 h (n.1 u) else 0

/-- Extend-by-zero of primed degree-two families from an open subscheme. -/
def degreeTwoExtendByZero :
    degreeTwoLocallyFinite ((U.ι ≫ p).relativeDimensionFunction δ) (k + 2) →+
      degreeTwoLocallyFinite (p.relativeDimensionFunction δ) (k + 2) where
  toFun n := ⟨degreeTwoExtendByZero_toFun p δ U k n, sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- Underlying coefficients of primed degree-two closed pullback. -/
def degreeTwoClosedPullback_toFun
    (n : degreeTwoLocallyFinite (p.relativeDimensionFunction δ) (k + 2)) :
    degreeTwoCoefficients
      ((reducedClosedComplementι U ≫ p).relativeDimensionFunction δ) (k + 2) :=
  fun y ↦ mapRestrictClosed U 2 y.1
    (n.1 ⟨reducedClosedComplementι U y.1,
      (relativeDimensionFunction_closed p δ U y.1).trans y.2⟩)

/-- Closed pullback of primed degree-two families to the reduced complement. -/
def degreeTwoClosedPullback :
    degreeTwoLocallyFinite (p.relativeDimensionFunction δ) (k + 2) →+
      degreeTwoLocallyFinite
        ((reducedClosedComplementι U ≫ p).relativeDimensionFunction δ) (k + 2) where
  toFun n := ⟨degreeTwoClosedPullback_toFun p δ U k n, sorry⟩
  map_zero' := sorry
  map_add' := sorry

open Classical in
/-- Underlying coefficients of primed degree-one closed pushforward. -/
def degreeOneClosedPushforward_toFun (n : locallyFinite
    ((reducedClosedComplementι U ≫ p).relativeDimensionFunction δ) (k + 1)) :
    degreeOneCoefficients (p.relativeDimensionFunction δ) (k + 1) :=
  fun x ↦ ∑ᶠ y : {y : reducedClosedComplement U //
      (reducedClosedComplementι U ≫ p).relativeDimensionFunction δ y = k + 1},
    if h : reducedClosedComplementι U y.1 = x.1 then
      mapAlongClosed U 1 y.1 x.1 h (n.1 y)
    else
      0

/-- Closed pushforward of primed degree-one families from the reduced complement. -/
def degreeOneClosedPushforward :
    locallyFinite ((reducedClosedComplementι U ≫ p).relativeDimensionFunction δ) (k + 1) →+
      locallyFinite (p.relativeDimensionFunction δ) (k + 1) where
  toFun n := ⟨degreeOneClosedPushforward_toFun p δ U k n, sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- Underlying coefficients of primed degree-one open pullback. -/
def degreeOneOpenPullback_toFun
    (n : locallyFinite (p.relativeDimensionFunction δ) (k + 1)) :
    degreeOneCoefficients ((U.ι ≫ p).relativeDimensionFunction δ) (k + 1) :=
  fun u ↦ mapRestrictOpen U 1 u.1
    (n.1 ⟨U.ι u.1, (relativeDimensionFunction_open p δ U u.1).trans u.2⟩)

/-- Open pullback of primed degree-one families to an open subscheme. -/
def degreeOneOpenPullback :
    locallyFinite (p.relativeDimensionFunction δ) (k + 1) →+
      locallyFinite ((U.ι ≫ p).relativeDimensionFunction δ) (k + 1) where
  toFun n := ⟨degreeOneOpenPullback_toFun p δ U k n, sorry⟩
  map_zero' := sorry
  map_add' := sorry

open Classical in
/-- Underlying coefficients of primed degree-one extend-by-zero. -/
def degreeOneExtendByZero_toFun (n : locallyFinite
    ((U.ι ≫ p).relativeDimensionFunction δ) (k + 1)) :
    degreeOneCoefficients (p.relativeDimensionFunction δ) (k + 1) :=
  fun x ↦ ∑ᶠ u : {u : U.toScheme // (U.ι ≫ p).relativeDimensionFunction δ u = k + 1},
    if h : U.ι u.1 = x.1 then mapAlongOpen U 1 u.1 x.1 h (n.1 u) else 0

/-- Extend-by-zero of primed degree-one families from an open subscheme. -/
def degreeOneExtendByZero :
    locallyFinite ((U.ι ≫ p).relativeDimensionFunction δ) (k + 1) →+
      locallyFinite (p.relativeDimensionFunction δ) (k + 1) where
  toFun n := ⟨degreeOneExtendByZero_toFun p δ U k n, sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- Underlying coefficients of primed degree-one closed pullback. -/
def degreeOneClosedPullback_toFun
    (n : locallyFinite (p.relativeDimensionFunction δ) (k + 1)) :
    degreeOneCoefficients
      ((reducedClosedComplementι U ≫ p).relativeDimensionFunction δ) (k + 1) :=
  fun y ↦ mapRestrictClosed U 1 y.1
    (n.1 ⟨reducedClosedComplementι U y.1,
      (relativeDimensionFunction_closed p δ U y.1).trans y.2⟩)

/-- Closed pullback of primed degree-one families to the reduced complement. -/
def degreeOneClosedPullback :
    locallyFinite (p.relativeDimensionFunction δ) (k + 1) →+
      locallyFinite ((reducedClosedComplementι U ≫ p).relativeDimensionFunction δ) (k + 1) where
  toFun n := ⟨degreeOneClosedPullback_toFun p δ U k n, sorry⟩
  map_zero' := sorry
  map_add' := sorry

open Classical in
/-- Underlying coefficients of primed degree-zero closed pushforward. -/
def degreeZeroClosedPushforward_toFun (n : CycleGroup.Pointwise.locallyFinite
    ((reducedClosedComplementι U ≫ p).relativeDimensionFunction δ) k) :
    CycleGroup.Pointwise.Coefficients (p.relativeDimensionFunction δ) k :=
  fun x ↦ ∑ᶠ y : {y : reducedClosedComplement U //
      (reducedClosedComplementι U ≫ p).relativeDimensionFunction δ y = k},
    if h : reducedClosedComplementι U y.1 = x.1 then
      mapAlongClosed U 0 y.1 x.1 h (n.1 y)
    else
      0

/-- Closed pushforward of primed degree-zero families from the reduced complement. -/
def degreeZeroClosedPushforward :
    CycleGroup.Pointwise.locallyFinite
        ((reducedClosedComplementι U ≫ p).relativeDimensionFunction δ) k →+
      CycleGroup.Pointwise.locallyFinite (p.relativeDimensionFunction δ) k where
  toFun n := ⟨degreeZeroClosedPushforward_toFun p δ U k n, sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- Underlying coefficients of primed degree-zero open pullback. -/
def degreeZeroOpenPullback_toFun
    (n : CycleGroup.Pointwise.locallyFinite (p.relativeDimensionFunction δ) k) :
    CycleGroup.Pointwise.Coefficients ((U.ι ≫ p).relativeDimensionFunction δ) k :=
  fun u ↦ mapRestrictOpen U 0 u.1
    (n.1 ⟨U.ι u.1, (relativeDimensionFunction_open p δ U u.1).trans u.2⟩)

/-- Open pullback of primed degree-zero families to an open subscheme. -/
def degreeZeroOpenPullback :
    CycleGroup.Pointwise.locallyFinite (p.relativeDimensionFunction δ) k →+
      CycleGroup.Pointwise.locallyFinite ((U.ι ≫ p).relativeDimensionFunction δ) k where
  toFun n := ⟨degreeZeroOpenPullback_toFun p δ U k n, sorry⟩
  map_zero' := sorry
  map_add' := sorry

open Classical in
/-- Underlying coefficients of primed degree-zero extend-by-zero. -/
def degreeZeroExtendByZero_toFun (n : CycleGroup.Pointwise.locallyFinite
    ((U.ι ≫ p).relativeDimensionFunction δ) k) :
    CycleGroup.Pointwise.Coefficients (p.relativeDimensionFunction δ) k :=
  fun x ↦ ∑ᶠ u : {u : U.toScheme // (U.ι ≫ p).relativeDimensionFunction δ u = k},
    if h : U.ι u.1 = x.1 then mapAlongOpen U 0 u.1 x.1 h (n.1 u) else 0

/-- Extend-by-zero of primed degree-zero families from an open subscheme. -/
def degreeZeroExtendByZero :
    CycleGroup.Pointwise.locallyFinite ((U.ι ≫ p).relativeDimensionFunction δ) k →+
      CycleGroup.Pointwise.locallyFinite (p.relativeDimensionFunction δ) k where
  toFun n := ⟨degreeZeroExtendByZero_toFun p δ U k n, sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- Underlying coefficients of primed degree-zero closed pullback. -/
def degreeZeroClosedPullback_toFun
    (n : CycleGroup.Pointwise.locallyFinite (p.relativeDimensionFunction δ) k) :
    CycleGroup.Pointwise.Coefficients
      ((reducedClosedComplementι U ≫ p).relativeDimensionFunction δ) k :=
  fun y ↦ mapRestrictClosed U 0 y.1
    (n.1 ⟨reducedClosedComplementι U y.1,
      (relativeDimensionFunction_closed p δ U y.1).trans y.2⟩)

/-- Closed pullback of primed degree-zero families to the reduced complement. -/
def degreeZeroClosedPullback :
    CycleGroup.Pointwise.locallyFinite (p.relativeDimensionFunction δ) k →+
      CycleGroup.Pointwise.locallyFinite
        ((reducedClosedComplementι U ≫ p).relativeDimensionFunction δ) k where
  toFun n := ⟨degreeZeroClosedPullback_toFun p δ U k n, sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- Closed pushforward of primed degree-two families followed by open pullback is zero. -/
theorem degreeTwoClosedPushforward_comp_openPullback :
    AddCommGrpCat.ofHom (degreeTwoClosedPushforward p δ U k) ≫
      AddCommGrpCat.ofHom (degreeTwoOpenPullback p δ U k) = 0 := sorry

/-- Closed pushforward of primed degree-one families followed by open pullback is zero. -/
theorem degreeOneClosedPushforward_comp_openPullback :
    AddCommGrpCat.ofHom (degreeOneClosedPushforward p δ U k) ≫
      AddCommGrpCat.ofHom (degreeOneOpenPullback p δ U k) = 0 := sorry

/-- Closed pushforward of primed degree-zero families followed by open pullback is zero. -/
theorem degreeZeroClosedPushforward_comp_openPullback :
    AddCommGrpCat.ofHom (degreeZeroClosedPushforward p δ U k) ≫
      AddCommGrpCat.ofHom (degreeZeroOpenPullback p δ U k) = 0 := sorry

/-- The primed degree-two localization short complex of an open subscheme. -/
def degreeTwoLocalizationComplex : ShortComplex Ab :=
  ShortComplex.mk (AddCommGrpCat.ofHom (degreeTwoClosedPushforward p δ U k))
    (AddCommGrpCat.ofHom (degreeTwoOpenPullback p δ U k))
    (degreeTwoClosedPushforward_comp_openPullback p δ U k)

/-- The primed degree-one localization short complex of an open subscheme. -/
def degreeOneLocalizationComplex : ShortComplex Ab :=
  ShortComplex.mk (AddCommGrpCat.ofHom (degreeOneClosedPushforward p δ U k))
    (AddCommGrpCat.ofHom (degreeOneOpenPullback p δ U k))
    (degreeOneClosedPushforward_comp_openPullback p δ U k)

/-- The primed degree-zero localization short complex of an open subscheme. -/
def degreeZeroLocalizationComplex : ShortComplex Ab :=
  ShortComplex.mk (AddCommGrpCat.ofHom (degreeZeroClosedPushforward p δ U k))
    (AddCommGrpCat.ofHom (degreeZeroOpenPullback p δ U k))
    (degreeZeroClosedPushforward_comp_openPullback p δ U k)

/-- Extend-by-zero is a section of primed degree-two open pullback, and closed pullback is a
retraction of closed pushforward. -/
def degreeTwoLocalizationSplitting : (degreeTwoLocalizationComplex p δ U k).Splitting where
  r := AddCommGrpCat.ofHom (degreeTwoClosedPullback p δ U k)
  s := AddCommGrpCat.ofHom (degreeTwoExtendByZero p δ U k)
  f_r := sorry
  s_g := sorry
  id := sorry

/-- Extend-by-zero is a section of primed degree-one open pullback, and closed pullback is a
retraction of closed pushforward. -/
def degreeOneLocalizationSplitting : (degreeOneLocalizationComplex p δ U k).Splitting where
  r := AddCommGrpCat.ofHom (degreeOneClosedPullback p δ U k)
  s := AddCommGrpCat.ofHom (degreeOneExtendByZero p δ U k)
  f_r := sorry
  s_g := sorry
  id := sorry

/-- Extend-by-zero is a section of primed degree-zero open pullback, and closed pullback is a
retraction of closed pushforward. -/
def degreeZeroLocalizationSplitting : (degreeZeroLocalizationComplex p δ U k).Splitting where
  r := AddCommGrpCat.ofHom (degreeZeroClosedPullback p δ U k)
  s := AddCommGrpCat.ofHom (degreeZeroExtendByZero p δ U k)
  f_r := sorry
  s_g := sorry
  id := sorry

/-- Open pullback of primed degree-two families splits extend-by-zero. -/
theorem degreeTwoOpenPullback_comp_extendByZero :
    (degreeTwoOpenPullback p δ U k).comp (degreeTwoExtendByZero p δ U k) =
      AddMonoidHom.id _ := sorry

/-- Open pullback of primed degree-one families splits extend-by-zero. -/
theorem degreeOneOpenPullback_comp_extendByZero :
    (degreeOneOpenPullback p δ U k).comp (degreeOneExtendByZero p δ U k) =
      AddMonoidHom.id _ := sorry

/-- Open pullback of primed degree-zero families splits extend-by-zero. -/
theorem degreeZeroOpenPullback_comp_extendByZero :
    (degreeZeroOpenPullback p δ U k).comp (degreeZeroExtendByZero p δ U k) =
      AddMonoidHom.id _ := sorry

end AlgebraicGeometry.ChowGroup.Pointwise

namespace AlgebraicGeometry.ChowGroup.FirstHigher

open AlgebraicGeometry.ChowGroup AlgebraicGeometry.ChowGroup.Pointwise

variable {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
variable (U : X.Opens) (k : ℤ)

/-- Closed pushforward of primed Milnor complexes from the reduced complement. -/
def milnorComplexClosedPushforward :
    AlgebraicGeometry.ChowGroup.milnorComplex (reducedClosedComplementι U ≫ p) δ k ⟶
      AlgebraicGeometry.ChowGroup.milnorComplex p δ k :=
  ShortComplex.homMk (AddCommGrpCat.ofHom (degreeTwoClosedPushforward p δ U k))
    (AddCommGrpCat.ofHom (degreeOneClosedPushforward p δ U k))
    (AddCommGrpCat.ofHom (degreeZeroClosedPushforward p δ U k)) sorry sorry

/-- Open pullback of primed Milnor complexes to an open subscheme. -/
def milnorComplexOpenPullback :
    AlgebraicGeometry.ChowGroup.milnorComplex p δ k ⟶
      AlgebraicGeometry.ChowGroup.milnorComplex (U.ι ≫ p) δ k :=
  ShortComplex.homMk (AddCommGrpCat.ofHom (degreeTwoOpenPullback p δ U k))
    (AddCommGrpCat.ofHom (degreeOneOpenPullback p δ U k))
    (AddCommGrpCat.ofHom (degreeZeroOpenPullback p δ U k)) sorry sorry

/-- Closed pushforward of first higher Chow groups from the reduced complement. -/
def closedPushforward :
    @Pointwise.firstHigher (reducedClosedComplement U)
        (LocallyOfFiniteType.isLocallyNoetherian (reducedClosedComplementι U ≫ p))
        ((reducedClosedComplementι U ≫ p).relativeDimensionFunction δ) inferInstance k →+
      @Pointwise.firstHigher X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k :=
  ((@Pointwise.firstHigherIso (reducedClosedComplement U)
          (LocallyOfFiniteType.isLocallyNoetherian (reducedClosedComplementι U ≫ p))
          ((reducedClosedComplementι U ≫ p).relativeDimensionFunction δ) inferInstance k).hom ≫
      ShortComplex.homologyMap (milnorComplexClosedPushforward p δ U k) ≫
      (@Pointwise.firstHigherIso X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k).inv).hom

/-- Open pullback of first higher Chow groups to an open subscheme. -/
def openPullback :
    @Pointwise.firstHigher X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k →+
      @Pointwise.firstHigher U.toScheme (LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ p))
        ((U.ι ≫ p).relativeDimensionFunction δ) inferInstance k :=
  ((@Pointwise.firstHigherIso X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance k).hom ≫
      ShortComplex.homologyMap (milnorComplexOpenPullback p δ U k) ≫
      (@Pointwise.firstHigherIso U.toScheme (LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ p))
        ((U.ι ≫ p).relativeDimensionFunction δ) inferInstance k).inv).hom

/-- The connecting homomorphism of the localization sequence, sending a first higher Chow
class on `U` to an ordinary Chow class on the reduced complement. -/
def connecting_onKer
    (z : AddMonoidHom.ker
      (AlgebraicGeometry.ChowGroup.milnorComplex (U.ι ≫ p) δ k).g.hom) :
    CycleGroup.Pointwise.locallyFinite
      ((reducedClosedComplementι U ≫ p).relativeDimensionFunction δ) k :=
  degreeZeroClosedPullback p δ U k
    ((AlgebraicGeometry.ChowGroup.milnorComplex p δ k).g.hom
      (degreeOneExtendByZero p δ U k z.1))

/-- The connecting homomorphism `CH^M_k(U, 1) → CH_k(Y)` of the localization sequence. -/
def connecting :
    @Pointwise.firstHigher U.toScheme (LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ p))
        ((U.ι ≫ p).relativeDimensionFunction δ) inferInstance k →+
      @ChowGroup (reducedClosedComplement U)
        (LocallyOfFiniteType.isLocallyNoetherian (reducedClosedComplementι U ≫ p))
        ((reducedClosedComplementι U ≫ p).relativeDimensionFunction δ) inferInstance k :=
  (@Pointwise.homologyZeroIso (reducedClosedComplement U)
        (LocallyOfFiniteType.isLocallyNoetherian (reducedClosedComplementι U ≫ p))
        ((reducedClosedComplementι U ≫ p).relativeDimensionFunction δ) inferInstance k).toAddMonoidHom.comp
    (QuotientAddGroup.lift
      (AddMonoidHom.range
        (AlgebraicGeometry.ChowGroup.milnorComplex (U.ι ≫ p) δ k).abToCycles)
      { toFun := fun z ↦ QuotientAddGroup.mk (connecting_onKer p δ U k z)
        map_zero' := sorry
        map_add' := sorry } sorry)

/-- The six-term localization sequence of first higher Chow groups and ordinary Chow groups. -/
def localizationArrows : ComposableArrows Ab 5 :=
  ComposableArrows.mk₅ (AddCommGrpCat.ofHom (closedPushforward p δ U k))
    (AddCommGrpCat.ofHom (openPullback p δ U k))
    (AddCommGrpCat.ofHom (connecting p δ U k))
    (Localization.complex p δ U k).f (Localization.complex p δ U k).g

/-- Closed pushforward on first higher Chow groups is induced by the morphism of primed
Milnor complexes. -/
theorem closedPushforward_apply
    (α : @Pointwise.firstHigher (reducedClosedComplement U)
      (LocallyOfFiniteType.isLocallyNoetherian (reducedClosedComplementι U ≫ p))
      ((reducedClosedComplementι U ≫ p).relativeDimensionFunction δ) inferInstance k) :
    closedPushforward p δ U k α =
      (@Pointwise.firstHigherIso X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance k).inv
        (ShortComplex.homologyMap (milnorComplexClosedPushforward p δ U k)
          ((@Pointwise.firstHigherIso (reducedClosedComplement U)
            (LocallyOfFiniteType.isLocallyNoetherian (reducedClosedComplementι U ≫ p))
            ((reducedClosedComplementι U ≫ p).relativeDimensionFunction δ) inferInstance k).hom α)) := sorry

/-- Open pullback on first higher Chow groups is induced by the morphism of primed
Milnor complexes. -/
theorem openPullback_apply
    (α : @Pointwise.firstHigher X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance k) :
    openPullback p δ U k α =
      (@Pointwise.firstHigherIso U.toScheme (LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ p))
          ((U.ι ≫ p).relativeDimensionFunction δ) inferInstance k).inv
        (ShortComplex.homologyMap (milnorComplexOpenPullback p δ U k)
          ((@Pointwise.firstHigherIso X (LocallyOfFiniteType.isLocallyNoetherian p)
            (p.relativeDimensionFunction δ) inferInstance k).hom α)) := sorry

end AlgebraicGeometry.ChowGroup.FirstHigher
