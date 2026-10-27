/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Mixed.Triangulated
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated
open AlgebraicGeometry

universe u

/- Lemma 42.52.4. The full mixed localized Chern series is multiplicative
for a distinguished perfect triangle under the two off-center rank bounds
and any of the four connecting-map finiteness alternatives. -/
@[stacks 0FBD] #check
  (AlgebraicGeometry.LocalizedChern.mixedChernClass_distinguished_family :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
      {δ : S → ℤ} [IsDimensionFunction δ]
      {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
      (i : Z ⟶ X.left) [IsClosedImmersion i]
      (T : Triangle (RingedSpace.ModuleDerived X.left.toRingedSpace))
      (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.left.toRingedSpace))
      (h1 : RingedSpace.ModuleDerived.IsPerfect T.obj₁)
      (h2 : RingedSpace.ModuleDerived.IsPerfect T.obj₂)
      (h3 : RingedSpace.ModuleDerived.IsPerfect T.obj₃)
      (p1 p3 : ℕ)
      (rank1 : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
        (LocalizedChern.restrictAway i T.obj₁) 0 p1)
      (rank3 : Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
        (LocalizedChern.restrictAway i T.obj₃) 0 p3)
      (hfin :
        (∃ (Y : Scheme.{u}) (f : Y ⟶ X.left), IsEnvelope f ∧
          RingedSpace.ModuleDerived.Morphism.HasLocallyBoundedFiniteLocallyFree
            ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₃)) ∨
        RingedSpace.ModuleDerived.Morphism.HasLocallyBoundedFiniteLocallyFree T.mor₃ ∨
        (∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left)) ∨
        CompactSpace X.left)
      (classes : ChernClass.Theory δ X.hom),
      LocalizedChern.EnvelopeClasses.mixedChernClass i classes T.obj₂ h2
        (ChernClass.Derived.isDefined_obj₂_of_connecting
          (noetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom) T hT h1 h2 h3 hfin)
        (p1 + p3) (LocalizedChern.rankBound_obj₂ i T hT p1 p3 rank1 rank3) =
      BivariantClass.Cutoff.familyMul δ
        (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) p1 p3
        (LocalizedChern.EnvelopeClasses.mixedChernClass i classes T.obj₁ h1
          (ChernClass.Derived.isDefined_obj₁_of_connecting
          (noetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom) T hT h1 h2 h3 hfin)
          p1 rank1)
        (LocalizedChern.EnvelopeClasses.mixedChernClass i classes T.obj₃ h3
          (ChernClass.Derived.isDefined_obj₃_of_connecting
          (noetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom) T hT h1 h2 h3 hfin)
          p3 rank3))
