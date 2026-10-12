/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_47_9
public import stacks_project.Chap42.Lemma_42_47_11
public import stacks_project.Chap42.Lemma_42_49_5

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open ChernClass.Derived

/-- The class-at-zero construction preserves addition of localized bivariant classes. -/
theorem classAtZero_add
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (p : ℤ)
    (localized localized' : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) p) :
    classAtZero delta i b p (localized + localized') =
      classAtZero delta i b p localized + classAtZero delta i b p localized' := sorry

/-- The canonical restriction of a derived module on the compactification to the
inverse image of `Z` in the infinity fibre. -/
abbrev infinityRestriction
    {S : Scheme.{u}} {X : Over S} {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) (b : W ⟶ ProjectiveLineFamily.space X)
    (Q : RingedSpace.ModuleDerived W.toRingedSpace) :
    RingedSpace.ModuleDerived (infinityCenter i b).left.toRingedSpace :=
  (RingedSpace.modulePullbackDerived
    ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
      (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q

/-- `infinityRestriction` is the derived pullback along the canonical map from the
infinity center to the compactification. -/
theorem infinityRestriction_def
    {S : Scheme.{u}} {X : Over S} {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) (b : W ⟶ ProjectiveLineFamily.space X)
    (Q : RingedSpace.ModuleDerived W.toRingedSpace) :
    infinityRestriction i b Q =
      (RingedSpace.modulePullbackDerived
        ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
          (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q := sorry

/-- Lemma 42.49.8: for two perfect derived objects on the compactification whose Chern
classes are defined and whose restrictions to `T` vanish, the Newton class at zero of
their binary biproduct is the sum of their Newton classes at zero. -/
@[stacks 0FAZ]
theorem newtonClassAtZero_biprod
    {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ} [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q Q' : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfectQ : RingedSpace.ModuleDerived.IsPerfect Q)
    (perfectQ' : RingedSpace.ModuleDerived.IsPerfect Q')
    (definedQ : ChernClass.Derived.IsDefined Q)
    (definedQ' : ChernClass.Derived.IsDefined Q')
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
          (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (p : ℕ)
    (restrictionZeroQ : IsZero
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q))
    (restrictionZeroQ' : IsZero
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q'))
    (classes : ChernClass.Theory delta X.hom)
    (localizedQ localizedQ' localizedBiprod : BivariantClass delta
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) (p : ℤ))
    (hlocalizedQ : IsInfinityLocalizedExtension delta i b t (p : ℤ)
      (ChernClass.Derived.newtonClass delta (infinityCenter i b).hom
        (classes.reanchor (infinityCenter i b))
        (infinityRestriction i b Q)
        (RingedSpace.modulePullbackDerived_isPerfect
          ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
            (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom Q perfectQ)
        (IsDefined.pullback
          ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
            (BivariantClass.GysinAtInfinity.infinityInclusion X b).left) definedQ) p)
      localizedQ)
    (hlocalizedQ' : IsInfinityLocalizedExtension delta i b t (p : ℤ)
      (ChernClass.Derived.newtonClass delta (infinityCenter i b).hom
        (classes.reanchor (infinityCenter i b))
        (infinityRestriction i b Q')
        (RingedSpace.modulePullbackDerived_isPerfect
          ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
            (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom Q' perfectQ')
        (IsDefined.pullback
          ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
            (BivariantClass.GysinAtInfinity.infinityInclusion X b).left) definedQ') p)
      localizedQ')
    (hlocalizedBiprod : IsInfinityLocalizedExtension delta i b t (p : ℤ)
      (ChernClass.Derived.newtonClass delta (infinityCenter i b).hom
        (classes.reanchor (infinityCenter i b))
        (infinityRestriction i b Q ⊞ infinityRestriction i b Q')
        ((RingedSpace.modulePullbackDerived_isPerfect
          ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
            (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom Q perfectQ).biprod
          (RingedSpace.modulePullbackDerived_isPerfect
            ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
              (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom Q' perfectQ'))
        ((IsDefined.pullback
          ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
            (BivariantClass.GysinAtInfinity.infinityInclusion X b).left) definedQ).biprod
          (IsDefined.pullback
            ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
                (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).left ≫
              (BivariantClass.GysinAtInfinity.infinityInclusion X b).left) definedQ')) p)
      localizedBiprod) :
    classAtZero delta i b (p : ℤ) localizedBiprod =
      classAtZero delta i b (p : ℤ) localizedQ +
        classAtZero delta i b (p : ℤ) localizedQ' := sorry

end AlgebraicGeometry.LocalizedChern
