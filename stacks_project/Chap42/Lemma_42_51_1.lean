/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_51_1_Intersection
public import stacks_project.Chap42.Definition_42_50_3_LocalizedClasses
public import stacks_project.Chap42.Lemma_42_48_2_BaseChange
public import stacks_project.Chap42.Lemma_42_49_5_Commutation
public import stacks_project.Chap42.Lemma_42_50_9

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open BivariantClass BivariantClass.IteratedIntersection ChernClass.Derived

/-- A closed subscheme of an `S`-scheme locally of finite type is locally of finite
type over `S`. -/
instance closedOverSourceLocallyOfFiniteType
    {S : Scheme.{u}} {X : Over S} [LocallyOfFiniteType X.hom]
    {Z : Scheme.{u}} (i : Z ⟶ X.left) [IsClosedImmersion i] :
    LocallyOfFiniteType (Over.mk (i ≫ X.hom)).hom := sorry

/-- The inverse image in a compactification of the projective-line family over a
closed subscheme. -/
def deformationCenterInclusion
    {S : Scheme.{u}} {X : Over S} {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) (b : W ⟶ ProjectiveLineFamily.space X) :
    pullback b (ProjectiveLineFamily.map
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) ⟶ W :=
  pullback.fst b (ProjectiveLineFamily.map
    (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))

/-- `deformationCenterInclusion` is the first projection of its defining pullback. -/
theorem deformationCenterInclusion_def
    {S : Scheme.{u}} {X : Over S} {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) (b : W ⟶ ProjectiveLineFamily.space X) :
    deformationCenterInclusion i b = pullback.fst b (ProjectiveLineFamily.map
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) := sorry

/-- The deformation-center inclusion is a closed immersion. -/
instance deformationCenterInclusionIsClosedImmersion
    {S : Scheme.{u}} {X : Over S} {Z W : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) :
    IsClosedImmersion (deformationCenterInclusion i b) := sorry

/-- A perfect derived module with a locally bounded finite locally free representative
has defined Chern classes. -/
theorem isDefined_of_representative
    {X : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (representative :
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative E) :
    ChernClass.Derived.IsDefined E := sorry

/-- The ordered intersection of a finite family of closed subschemes is locally of
finite type over the base. -/
instance closedIntersectionLocallyOfFiniteType
    {S : Scheme.{u}} {X : Over S} [LocallyOfFiniteType X.hom] {n : ℕ}
    (Z : Fin (n + 1) → Scheme.{u}) (i : ∀ j, Z j ⟶ X.left)
    [∀ j, IsClosedImmersion (i j)] :
    LocallyOfFiniteType
      (object (fun j ↦ Over.mk (i j ≫ X.hom))
        (fun j ↦ Over.homMk (i j))).hom := sorry

/-- The maps from a finite family of closed subschemes to their common ambient
over-object form a pointwise proper family. -/
instance closedFamilyProper
    {S : Scheme.{u}} {X : Over S} {n : ℕ}
    (Z : Fin (n + 1) → Scheme.{u}) (i : ∀ j, Z j ⟶ X.left)
    [∀ j, IsClosedImmersion (i j)] :
    ∀ j, IsProper
      (Over.homMk (i j) : Over.mk (i j ≫ X.hom) ⟶ X).left := sorry

/-- A finite family of closed subschemes of a locally finite-type `S`-scheme is
pointwise locally of finite type over `S`. -/
instance closedFamilyLocallyOfFiniteType
    {S : Scheme.{u}} {X : Over S} [LocallyOfFiniteType X.hom] {n : ℕ}
    (Z : Fin (n + 1) → Scheme.{u}) (i : ∀ j, Z j ⟶ X.left)
    [∀ j, IsClosedImmersion (i j)] :
    ∀ j, LocallyOfFiniteType (Over.mk (i j ≫ X.hom)).hom := sorry

/-- The ordered intersection of the inverse images of closed subschemes in the
infinity fibre is locally of finite type over the base. -/
instance infinityIntersectionLocallyOfFiniteType
    {S : Scheme.{u}} {X : Over S} [LocallyOfFiniteType X.hom] {W : Scheme.{u}}
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    {n : ℕ} (Z : Fin (n + 1) → Scheme.{u}) (i : ∀ j, Z j ⟶ X.left)
    [∀ j, IsClosedImmersion (i j)] :
    LocallyOfFiniteType
      (object (fun j ↦ infinityCenter (i j) b)
        (fun j ↦ pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
          (Over.homMk (i j) : Over.mk (i j ≫ X.hom) ⟶ X))).hom := sorry

/-- The projections from the inverse images of a finite family of closed subschemes
to the infinity fibre form a pointwise proper family. -/
instance infinityCenterProjectionFamilyProper
    {S : Scheme.{u}} {X : Over S} {W : Scheme.{u}}
    (b : W ⟶ ProjectiveLineFamily.space X)
    {n : ℕ} (Z : Fin (n + 1) → Scheme.{u}) (i : ∀ j, Z j ⟶ X.left)
    [∀ j, IsClosedImmersion (i j)] :
    ∀ j, IsProper
      (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
        (Over.homMk (i j) : Over.mk (i j ≫ X.hom) ⟶ X)).left := sorry

/-- The inverse images of a finite family of closed subschemes in a locally
finite-type infinity fibre are pointwise locally of finite type over the base. -/
instance infinityCenterFamilyLocallyOfFiniteType
    {S : Scheme.{u}} {X : Over S} [LocallyOfFiniteType X.hom] {W : Scheme.{u}}
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    {n : ℕ} (Z : Fin (n + 1) → Scheme.{u}) (i : ∀ j, Z j ⟶ X.left)
    [∀ j, IsClosedImmersion (i j)] :
    ∀ j, LocallyOfFiniteType (infinityCenter (i j) b).hom := sorry

/-- Lemma 42.51.1 (1): for a nonempty finite family satisfying the zero-restriction
alternative, the ordered product of the localized Newton classes at zero is the proper
pushforward of the ordered product of the infinity-localized Newton classes followed by
the Gysin-at-infinity class. -/
@[stacks 0FE7]
theorem iteratedNewton_eq_pushforward
    {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ} [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {W : Scheme.{u}}
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    {n : ℕ} (Z : Fin (n + 1) → Scheme.{u}) (i : ∀ j, Z j ⟶ X.left)
    [∀ j, IsClosedImmersion (i j)]
    (Q : ∀ j, RingedSpace.ModuleDerived W.toRingedSpace)
    (p : Fin (n + 1) → ℕ)
    (T : Fin (n + 1) → Scheme.{u})
    (t : ∀ j, T j ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [∀ j, IsClosedImmersion (t j)]
    (classes : ChernClass.Theory delta X.hom)
    (perfect : ∀ j, RingedSpace.ModuleDerived.IsPerfect (Q j))
    (containsComplement : ∀ j,
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
          (Set.range (i j).base)ᶜ ⊆ Set.range (t j).base)
    (onT : ∀ j, RestrictionCondition
      (t j ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left)
      (Q j) (p j) .vanishing)
    (offCenter : ∀ j, OffCenterCondition
      (deformationCenterInclusion (i j) b)
      (Q j) (p j) .vanishing)
    (representative : ∀ j,
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative (Q j)) :
    let infinityPerfect : ∀ j, RingedSpace.ModuleDerived.IsPerfect
        (infinityCenterRestriction (i j) b (Q j)) := fun j ↦
      RingedSpace.modulePullbackDerived_isPerfect
        ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk (i j) : Over.mk (i j ≫ X.hom) ⟶ X)).left ≫
          (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom
        (Q j) (perfect j)
    let infinityDefined : ∀ j, ChernClass.Derived.IsDefined
        (infinityCenterRestriction (i j) b (Q j)) := fun j ↦
      IsDefined.pullback
        ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk (i j) : Over.mk (i j ≫ X.hom) ⟶ X)).left ≫
          (BivariantClass.GysinAtInfinity.infinityInclusion X b).left)
        (isDefined_of_representative (Q j) (representative j))
    ∀ (localized : ∀ j, BivariantClass delta
          (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk (i j) : Over.mk (i j ≫ X.hom) ⟶ X)) (p j : ℤ))
      (localizedSpec : ∀ j, IsInfinityLocalizedExtension delta (i j) b (t j) (p j : ℤ)
        (infinityAmbientClass (i j) b classes (Q j) (p j) .vanishing
          (infinityPerfect j) (infinityDefined j)) (localized j)),
      mul delta (fun j ↦ Over.mk (i j ≫ X.hom))
          (fun j ↦ Over.homMk (i j)) (fun j ↦ (p j : ℤ))
          (fun j ↦ classAtZero delta (i j) b (p j : ℤ) (localized j)) =
        @BivariantClass.pushforwardComp S inferInstance delta inferInstance
          _ _ _ _ (infinityIntersectionLocallyOfFiniteType b Z i)
          (closedIntersectionLocallyOfFiniteType Z i) inferInstance inferInstance
          (baseChangeMap (BivariantClass.GysinAtInfinity.infinityToX X b)
            (fun j ↦ Over.mk (i j ≫ X.hom)) (fun j ↦ Over.homMk (i j)))
          (baseChangeMapProper (BivariantClass.GysinAtInfinity.infinityToX X b)
            (fun j ↦ Over.mk (i j ≫ X.hom)) (fun j ↦ Over.homMk (i j)))
          (toTarget (fun j ↦ Over.mk (i j ≫ X.hom)) (fun j ↦ Over.homMk (i j)))
          (toTarget
            (fun j ↦ infinityCenter (i j) b)
            (fun j ↦ pullback.fst
              (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk (i j) : Over.mk (i j ≫ X.hom) ⟶ X)))
          (BivariantClass.GysinAtInfinity.infinityToX X b)
          (baseChangeMap_factor
            (BivariantClass.GysinAtInfinity.infinityToX X b)
            (fun j ↦ Over.mk (i j ≫ X.hom)) (fun j ↦ Over.homMk (i j)))
          (degree (fun j ↦ (p j : ℤ)))
          (mul delta
            (fun j ↦ infinityCenter (i j) b)
            (fun j ↦ pullback.fst
              (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk (i j) : Over.mk (i j ≫ X.hom) ⟶ X))
            (fun j ↦ (p j : ℤ)) localized)
          (BivariantClass.gysinAtInfinity delta X b) := sorry

/-- Lemma 42.51.1 (2): for a nonempty finite family satisfying the rank-bound
alternative, the ordered product of the localized Chern classes at zero is the proper
pushforward of the ordered product of the infinity-localized Chern classes followed by
the Gysin-at-infinity class. -/
@[stacks 0FE7]
theorem iteratedChern_eq_pushforward
    {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ} [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {W : Scheme.{u}}
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    {n : ℕ} (Z : Fin (n + 1) → Scheme.{u}) (i : ∀ j, Z j ⟶ X.left)
    [∀ j, IsClosedImmersion (i j)]
    (Q : ∀ j, RingedSpace.ModuleDerived W.toRingedSpace)
    (p : Fin (n + 1) → ℕ)
    (T : Fin (n + 1) → Scheme.{u})
    (t : ∀ j, T j ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [∀ j, IsClosedImmersion (t j)]
    (classes : ChernClass.Theory delta X.hom)
    (perfect : ∀ j, RingedSpace.ModuleDerived.IsPerfect (Q j))
    (containsComplement : ∀ j,
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
          (Set.range (i j).base)ᶜ ⊆ Set.range (t j).base)
    (onT : ∀ j, RestrictionCondition
      (t j ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left)
      (Q j) (p j) .rankBound)
    (offCenter : ∀ j, OffCenterCondition
      (deformationCenterInclusion (i j) b)
      (Q j) (p j) .rankBound)
    (representative : ∀ j,
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative (Q j)) :
    let infinityPerfect : ∀ j, RingedSpace.ModuleDerived.IsPerfect
        (infinityCenterRestriction (i j) b (Q j)) := fun j ↦
      RingedSpace.modulePullbackDerived_isPerfect
        ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk (i j) : Over.mk (i j ≫ X.hom) ⟶ X)).left ≫
          (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom
        (Q j) (perfect j)
    let infinityDefined : ∀ j, ChernClass.Derived.IsDefined
        (infinityCenterRestriction (i j) b (Q j)) := fun j ↦
      IsDefined.pullback
        ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk (i j) : Over.mk (i j ≫ X.hom) ⟶ X)).left ≫
          (BivariantClass.GysinAtInfinity.infinityInclusion X b).left)
        (isDefined_of_representative (Q j) (representative j))
    ∀ (localized : ∀ j, BivariantClass delta
          (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk (i j) : Over.mk (i j ≫ X.hom) ⟶ X)) (p j : ℤ))
      (localizedSpec : ∀ j, IsInfinityLocalizedExtension delta (i j) b (t j) (p j : ℤ)
        (infinityAmbientClass (i j) b classes (Q j) (p j) .rankBound
          (infinityPerfect j) (infinityDefined j)) (localized j)),
      mul delta (fun j ↦ Over.mk (i j ≫ X.hom))
          (fun j ↦ Over.homMk (i j)) (fun j ↦ (p j : ℤ))
          (fun j ↦ classAtZero delta (i j) b (p j : ℤ) (localized j)) =
        @BivariantClass.pushforwardComp S inferInstance delta inferInstance
          _ _ _ _ (infinityIntersectionLocallyOfFiniteType b Z i)
          (closedIntersectionLocallyOfFiniteType Z i) inferInstance inferInstance
          (baseChangeMap (BivariantClass.GysinAtInfinity.infinityToX X b)
            (fun j ↦ Over.mk (i j ≫ X.hom)) (fun j ↦ Over.homMk (i j)))
          (baseChangeMapProper (BivariantClass.GysinAtInfinity.infinityToX X b)
            (fun j ↦ Over.mk (i j ≫ X.hom)) (fun j ↦ Over.homMk (i j)))
          (toTarget (fun j ↦ Over.mk (i j ≫ X.hom)) (fun j ↦ Over.homMk (i j)))
          (toTarget
            (fun j ↦ infinityCenter (i j) b)
            (fun j ↦ pullback.fst
              (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk (i j) : Over.mk (i j ≫ X.hom) ⟶ X)))
          (BivariantClass.GysinAtInfinity.infinityToX X b)
          (baseChangeMap_factor
            (BivariantClass.GysinAtInfinity.infinityToX X b)
            (fun j ↦ Over.mk (i j ≫ X.hom)) (fun j ↦ Over.homMk (i j)))
          (degree (fun j ↦ (p j : ℤ)))
          (mul delta
            (fun j ↦ infinityCenter (i j) b)
            (fun j ↦ pullback.fst
              (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk (i j) : Over.mk (i j ≫ X.hom) ⟶ X))
            (fun j ↦ (p j : ℤ)) localized)
          (BivariantClass.gysinAtInfinity delta X b) := sorry

end AlgebraicGeometry.LocalizedChern
