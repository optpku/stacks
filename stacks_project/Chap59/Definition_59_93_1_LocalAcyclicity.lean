/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.«59_93_0_1»
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

open EtaleVanishingCycles

/-- The geometric point obtained by postcomposing its scheme morphism. -/
abbrev GeometricPoint.imageHom {X S : Scheme.{u}} (xbar : GeometricPoint X) (f : X ⟶ S) :
    GeometricPoint S := GeometricPoint.of xbar.K (xbar.hom ≫ f)

/-- The image geometric point has the expected morphism. -/
theorem GeometricPoint.imageHom_hom {X S : Scheme.{u}}
    (xbar : GeometricPoint X) (f : X ⟶ S) :
    (xbar.imageHom f).hom = xbar.hom ≫ f := rfl

/-- The actual constant abelian étale sheaf with value ℤ/nℤ. -/
def constZModEtale (X : Scheme.{u}) (n : ℕ) : Coefficients X :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))

/-- Regard an abelian étale sheaf as a derived object concentrated in degree zero. -/
abbrev etaleSheafInDegreeZero {X : Scheme.{u}} (F : Coefficients X) : Complexes X :=
  (DerivedCategory.singleFunctor (Coefficients X) 0).obj F

/-- Local acyclicity at a geometric point: every actual derived restriction
from its strict henselization to a geometric vanishing-cycle fiber is an isomorphism.
This is the sections presentation of the stalk comparison, not an arbitrary family of maps. -/
class LocallyAcyclicAt {X S : Scheme.{u}} (f : X ⟶ S) (xbar : GeometricPoint X)
    (K : Complexes X) : Prop where
  /-- Isomorphism of the canonical comparison for each strict-henselization fiber. -/
  isIso_comparison :
    ∀ {RshS RshX : Type u}
      [CommRing RshS]
      [Algebra (S.presheaf.stalk (xbar.imageHom f).image) RshS]
      [IsStrictHenselizationOf (S.presheaf.stalk (xbar.imageHom f).image) RshS]
      [CommRing RshX] [Algebra (X.presheaf.stalk xbar.image) RshX]
      [IsStrictHenselizationOf (X.presheaf.stalk xbar.image) RshX]
      (h : strictHenselizationScheme X xbar RshX ⟶
        strictHenselizationScheme S (xbar.imageHom f) RshS)
      (h_induced : InducedStrictHenselizationTriangle f xbar h)
      (tbar : GeometricPoint (strictHenselizationScheme S (xbar.imageHom f) RshS)),
      IsIso (etaleCohomologyAlpha f xbar h h_induced tbar K)

/-- Local acyclicity relative to a derived étale coefficient object at all geometric points. -/
class LocallyAcyclicRelative {X S : Scheme.{u}} (f : X ⟶ S) (K : Complexes X) : Prop where
  /-- Pointwise local acyclicity for the same derived coefficient object. -/
  locallyAcyclicAt : ∀ xbar : GeometricPoint X, LocallyAcyclicAt f xbar K

/-- Relative local acyclicity supplies the property at each geometric point. -/
instance instLocallyAcyclicAt_of_locallyAcyclicRelative {X S : Scheme.{u}}
    (f : X ⟶ S) (K : Complexes X) [LocallyAcyclicRelative f K] (xbar : GeometricPoint X) :
    LocallyAcyclicAt f xbar K := LocallyAcyclicRelative.locallyAcyclicAt xbar

/-- Relative local acyclicity is precisely its pointwise condition. -/
theorem locallyAcyclicRelative_iff {X S : Scheme.{u}} (f : X ⟶ S) (K : Complexes X) :
    LocallyAcyclicRelative f K ↔ ∀ xbar : GeometricPoint X, LocallyAcyclicAt f xbar K :=
  ⟨fun h ↦ h.locallyAcyclicAt, fun h ↦ ⟨h⟩⟩

/-- Universal relative local acyclicity uses actual derived inverse image in every square. -/
class UniversallyLocallyAcyclicRelative {X S : Scheme.{u}} (f : X ⟶ S)
    (K : Complexes X) : Prop where
  /-- All cartesian base changes are locally acyclic for the pulled-back coefficients. -/
  of_baseChange : ∀ {X' S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (g : S' ⟶ S),
    IsPullback g' f' f g →
      LocallyAcyclicRelative f' ((derivedInverseImage g').obj K)

/-- The identity base change of a universally locally acyclic coefficient object. -/
instance locallyAcyclicRelative_of_universally {X S : Scheme.{u}}
    (f : X ⟶ S) (K : Complexes X) [UniversallyLocallyAcyclicRelative f K] :
    LocallyAcyclicRelative f K := sorry

/-- Ordinary local acyclicity tests the actual constant prime-to-characteristic coefficients. -/
class LocallyAcyclic {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  /-- Constant-coefficient local acyclicity at every geometric point. -/
  locallyAcyclicAt_const : ∀ (xbar : GeometricPoint X) (n : ℕ), (n : xbar.K) ≠ 0 →
    LocallyAcyclicAt f xbar (etaleSheafInDegreeZero (constZModEtale X n))

/-- The pointwise constant-coefficient consequence of ordinary local acyclicity. -/
theorem locallyAcyclicAt_of_locallyAcyclic {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyAcyclic f] (xbar : GeometricPoint X) (n : ℕ)
    (hn : (n : xbar.K) ≠ 0) :
    LocallyAcyclicAt f xbar (etaleSheafInDegreeZero (constZModEtale X n)) :=
  LocallyAcyclic.locallyAcyclicAt_const xbar n hn

/-- A morphism is universally locally acyclic when all its cartesian base changes are. -/
class UniversallyLocallyAcyclic {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  /-- Ordinary local acyclicity of every cartesian base change. -/
  of_baseChange : ∀ {X' S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (g : S' ⟶ S),
    IsPullback g' f' f g → LocallyAcyclic f'

/-- Universal local acyclicity implies local acyclicity by the identity square. -/
instance instLocallyAcyclic_of_universally {X S : Scheme.{u}}
    (f : X ⟶ S) [UniversallyLocallyAcyclic f] : LocallyAcyclic f := sorry

end AlgebraicGeometry.Scheme
