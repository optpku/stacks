/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.SchemeEtaleComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.EtaleComparison

/-! # Quasi-coherent derived comparison for represented algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Scheme.DerivedQCoh (SmallEtale epsilonStar)

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- A derived module on a represented algebraic space is the pullback of a
quasi-coherent derived module on the representing scheme when their canonical
images on the small étale site are isomorphic. -/
def isEpsilonStarPullback {S : Scheme.{u}} (U : Over S)
    (E : ModuleDerived (ofOver U)) (E0 : Scheme.DerivedQCoh U.left) : Prop :=
  IsIsomorphic
    ((AlgebraicSpace.DerivedQCoh.toEtaleDerived U).obj E)
    ((Scheme.DerivedQCoh.SmallEtale.inclusion U.left).obj
      ((Scheme.DerivedQCoh.epsilonStar U.left).obj E0))

/-- The pullback comparison is equivalent to the existence of an isomorphism
between the canonical images on the small étale site. -/
theorem isEpsilonStarPullback_iff {S : Scheme.{u}} (U : Over S)
    (E : ModuleDerived (ofOver U)) (E0 : Scheme.DerivedQCoh U.left) :
    isEpsilonStarPullback U E E0 ↔
      IsIsomorphic
        ((AlgebraicSpace.DerivedQCoh.toEtaleDerived U).obj E)
        ((Scheme.DerivedQCoh.SmallEtale.inclusion U.left).obj
          ((Scheme.DerivedQCoh.epsilonStar U.left).obj E0)) :=
  Iff.rfl

/-- Comparison isomorphism identifying the `schemeEtaleRingedHom` pushforward of `E` with
`ε* E0` on the small étale site of `U.left`. -/
abbrev EpsilonStarComparisonIso {S : Scheme.{u}} (U : Over S)
    (E : ModuleDerived (ofOver U)) (E0 : Scheme.DerivedQCoh U.left) :=
  (AlgebraicSpace.DerivedQCoh.toEtaleDerived U).obj E ≅
    (SmallEtale.inclusion U.left).obj ((epsilonStar U.left).obj E0)

/-- An étale/`ε*` comparison exists if and only if the corresponding comparison isomorphism
type is inhabited. -/
theorem nonempty_epsilonStarComparisonIso_iff {S : Scheme.{u}} (U : Over S)
    (E : ModuleDerived (ofOver U)) (E0 : Scheme.DerivedQCoh U.left) :
    Nonempty (EpsilonStarComparisonIso U E E0) ↔ isEpsilonStarPullback U E E0 :=
  Iff.rfl

/-- Given comparison isomorphisms `α` and `β`, there is a unique `e : E0 ≅ E0'` whose image
under étale inclusion after `ε*` equals `α.inv ≫ β`. -/
theorem epsilonStarComparison_unique {S : Scheme.{u}} (U : Over S)
    {E : ModuleDerived (ofOver U)} {E0 E0' : Scheme.DerivedQCoh U.left}
    (α : EpsilonStarComparisonIso U E E0) (β : EpsilonStarComparisonIso U E E0') :
    ∃! e : E0 ≅ E0',
      (epsilonStar U.left ⋙ SmallEtale.inclusion U.left).map e.hom = α.inv ≫ β.hom :=
  sorry

/-- If `E` lies in `D_QCoh(𝒪_{ofOver U})`, then `E` is the pullback of an object of
`D_QCoh(𝒪_{U.left})` along `ε*` after the `schemeEtaleRingedHom` identification, unique up
to a unique comparison-compatible isomorphism. -/
theorem qcohScheme_unique {S : Scheme.{u}} (U : Over S)
    {E : ModuleDerived (ofOver U)}
    (hE : derivedQuasiCoherentModuleProperty (ofOver U) E) :
    ∃ E0 : Scheme.DerivedQCoh U.left,
      isEpsilonStarPullback U E E0 ∧
        ∀ (E0' : Scheme.DerivedQCoh U.left),
          isEpsilonStarPullback U E E0' →
            ∀ (α : EpsilonStarComparisonIso U E E0)
              (β : EpsilonStarComparisonIso U E E0'),
              ∃! e : E0 ≅ E0',
                (epsilonStar U.left ⋙ SmallEtale.inclusion U.left).map e.hom =
                  α.inv ≫ β.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
