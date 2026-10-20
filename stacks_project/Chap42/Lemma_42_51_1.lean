module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.LocalizedChern.Iterated

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open BivariantClass BivariantClass.IteratedIntersection Scheme.IteratedIntersection ChernClass.Derived

/- Lemma 42.51.1: the ordered localized Newton product agrees with
proper pushforward from the intersection at infinity followed by Gysin at infinity. -/
@[stacks 0FE7] #check (AlgebraicGeometry.LocalizedChern.iteratedNewton_eq_pushforward :
  ∀
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
      (ProjectiveLineFamily.deformationCenterInclusion (i j) b)
      (Q j) (p j) .vanishing)
    (finiteness : ∀ j, TechnicalCondition
      (BivariantClass.GysinAtInfinity.compactification X b) (Q j)),
    let infinityPerfect : ∀ j, RingedSpace.ModuleDerived.IsPerfect
        (infinityCenterRestriction (i j) b (Q j)) := fun j ↦
      RingedSpace.modulePullbackDerived_isPerfect
        ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X)).left ≫
          (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom
        (Q j) (perfect j)
    let infinityDefined : ∀ j, ChernClass.Derived.IsDefined
        (infinityCenterRestriction (i j) b (Q j)) := fun j ↦
      IsDefined.pullback
        ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X)).left ≫
          (BivariantClass.GysinAtInfinity.infinityInclusion X b).left)
        (by
          apply (config := { synthAssignedInstances := false, allowSynthFailures := true }) Situation.isDefined
          case δ => exact delta
          case i => exact ProjectiveLineFamily.deformationCenterInclusion (i j) b
          case p => exact p j
          case mode => exact .vanishing
          all_goals try exact ProjectiveLineFamily.deformationCenterInclusionIsClosedImmersion (i j) b
          all_goals try infer_instance
          apply (config := { allowSynthFailures := true }) Situation.mk
          all_goals first
            | exact perfect j
            | exact offCenter j
            | exact finiteness j)
    ∀ (localized : ∀ j, BivariantClass delta
          (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X)) (p j : ℤ))
      (localizedSpec : ∀ j,
        let center := pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
          (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X)
        let inclusion : center ⟶ BivariantClass.GysinAtInfinity.infinityFiber X b :=
          pullback.fst _ _
        let displayIso : center ≅ Over.mk
            (inclusion.left ≫ (BivariantClass.GysinAtInfinity.infinityFiber X b).hom) :=
          Over.isoMk (Iso.refl _) ((Category.id_comp _).trans inclusion.w)
        BivariantClass.IsLocalizedExtension delta
          (BivariantClass.GysinAtInfinity.infinityFiber X b) (t j) inclusion.left (p j : ℤ)
          (BivariantClass.restrict delta displayIso.inv (𝟙 _) displayIso.inv
            IsPullback.of_id_snd (p j : ℤ)
            (infinityAmbientClass (i j) b classes (Q j) (p j) .vanishing
              (infinityPerfect j) (infinityDefined j)))
          (BivariantClass.restrict delta displayIso.inv (Over.homMk inclusion.left rfl) (𝟙 _)
            IsPullback.of_id_fst (p j : ℤ) (localized j))),
      mul delta (fun j ↦ Over.mk (i j ≫ X.hom))
          (fun j ↦ Over.homMk (i j) rfl) (fun j ↦ (p j : ℤ))
          (fun j ↦ BivariantClass.pushforwardComp delta
            (pullback.snd (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X))
            (Over.homMk (i j) rfl)
            (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X))
            (BivariantClass.GysinAtInfinity.infinityToX X b)
            pullback.condition (p j : ℤ) (localized j)
            (BivariantClass.gysinAtInfinity delta X b)) =
        BivariantClass.pushforwardComp delta
          (baseChangeMap (BivariantClass.GysinAtInfinity.infinityToX X b)
            (fun j ↦ Over.mk (i j ≫ X.hom)) (fun j ↦ Over.homMk (i j) rfl))
          (toTarget (fun j ↦ Over.mk (i j ≫ X.hom)) (fun j ↦ Over.homMk (i j) rfl))
          (toTarget
            (fun j ↦ (pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X)))
            (fun j ↦ pullback.fst
              (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X)))
          (BivariantClass.GysinAtInfinity.infinityToX X b)
          (baseChangeMap_factor
            (BivariantClass.GysinAtInfinity.infinityToX X b)
            (fun j ↦ Over.mk (i j ≫ X.hom)) (fun j ↦ Over.homMk (i j) rfl))
          (degree (fun j ↦ (p j : ℤ)))
          (mul delta
            (fun j ↦ (pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X)))
            (fun j ↦ pullback.fst
              (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X))
            (fun j ↦ (p j : ℤ)) localized)
          (BivariantClass.gysinAtInfinity delta X b))

/- Lemma 42.51.1: the ordered localized Chern product agrees with
proper pushforward from the intersection at infinity followed by Gysin at infinity. -/
@[stacks 0FE7] #check (AlgebraicGeometry.LocalizedChern.iteratedChern_eq_pushforward :
  ∀
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
      (ProjectiveLineFamily.deformationCenterInclusion (i j) b)
      (Q j) (p j) .rankBound)
    (finiteness : ∀ j, TechnicalCondition
      (BivariantClass.GysinAtInfinity.compactification X b) (Q j)),
    let infinityPerfect : ∀ j, RingedSpace.ModuleDerived.IsPerfect
        (infinityCenterRestriction (i j) b (Q j)) := fun j ↦
      RingedSpace.modulePullbackDerived_isPerfect
        ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X)).left ≫
          (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom
        (Q j) (perfect j)
    let infinityDefined : ∀ j, ChernClass.Derived.IsDefined
        (infinityCenterRestriction (i j) b (Q j)) := fun j ↦
      IsDefined.pullback
        ((pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X)).left ≫
          (BivariantClass.GysinAtInfinity.infinityInclusion X b).left)
        (by
          apply (config := { synthAssignedInstances := false, allowSynthFailures := true }) Situation.isDefined
          case δ => exact delta
          case i => exact ProjectiveLineFamily.deformationCenterInclusion (i j) b
          case p => exact p j
          case mode => exact .rankBound
          all_goals try exact ProjectiveLineFamily.deformationCenterInclusionIsClosedImmersion (i j) b
          all_goals try infer_instance
          apply (config := { allowSynthFailures := true }) Situation.mk
          all_goals first
            | exact perfect j
            | exact offCenter j
            | exact finiteness j)
    ∀ (localized : ∀ j, BivariantClass delta
          (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
            (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X)) (p j : ℤ))
      (localizedSpec : ∀ j,
        let center := pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
          (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X)
        let inclusion : center ⟶ BivariantClass.GysinAtInfinity.infinityFiber X b :=
          pullback.fst _ _
        let displayIso : center ≅ Over.mk
            (inclusion.left ≫ (BivariantClass.GysinAtInfinity.infinityFiber X b).hom) :=
          Over.isoMk (Iso.refl _) ((Category.id_comp _).trans inclusion.w)
        BivariantClass.IsLocalizedExtension delta
          (BivariantClass.GysinAtInfinity.infinityFiber X b) (t j) inclusion.left (p j : ℤ)
          (BivariantClass.restrict delta displayIso.inv (𝟙 _) displayIso.inv
            IsPullback.of_id_snd (p j : ℤ)
            (infinityAmbientClass (i j) b classes (Q j) (p j) .rankBound
              (infinityPerfect j) (infinityDefined j)))
          (BivariantClass.restrict delta displayIso.inv (Over.homMk inclusion.left rfl) (𝟙 _)
            IsPullback.of_id_fst (p j : ℤ) (localized j))),
      mul delta (fun j ↦ Over.mk (i j ≫ X.hom))
          (fun j ↦ Over.homMk (i j) rfl) (fun j ↦ (p j : ℤ))
          (fun j ↦ BivariantClass.pushforwardComp delta
            (pullback.snd (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X))
            (Over.homMk (i j) rfl)
            (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X))
            (BivariantClass.GysinAtInfinity.infinityToX X b)
            pullback.condition (p j : ℤ) (localized j)
            (BivariantClass.gysinAtInfinity delta X b)) =
        BivariantClass.pushforwardComp delta
          (baseChangeMap (BivariantClass.GysinAtInfinity.infinityToX X b)
            (fun j ↦ Over.mk (i j ≫ X.hom)) (fun j ↦ Over.homMk (i j) rfl))
          (toTarget (fun j ↦ Over.mk (i j ≫ X.hom)) (fun j ↦ Over.homMk (i j) rfl))
          (toTarget
            (fun j ↦ (pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X)))
            (fun j ↦ pullback.fst
              (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X)))
          (BivariantClass.GysinAtInfinity.infinityToX X b)
          (baseChangeMap_factor
            (BivariantClass.GysinAtInfinity.infinityToX X b)
            (fun j ↦ Over.mk (i j ≫ X.hom)) (fun j ↦ Over.homMk (i j) rfl))
          (degree (fun j ↦ (p j : ℤ)))
          (mul delta
            (fun j ↦ (pullback (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X)))
            (fun j ↦ pullback.fst
              (BivariantClass.GysinAtInfinity.infinityToX X b)
              (Over.homMk (i j) rfl : Over.mk (i j ≫ X.hom) ⟶ X))
            (fun j ↦ (p j : ℤ)) localized)
          (BivariantClass.gysinAtInfinity delta X b))

end AlgebraicGeometry.LocalizedChern
