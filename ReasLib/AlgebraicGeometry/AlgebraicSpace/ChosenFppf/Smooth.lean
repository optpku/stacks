/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf

/-!
# Smooth morphisms on chosen big fppf sites
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- A sheaf morphism is smooth if every commutative square from sheafified
representables with relatively étale vertical maps has smooth scheme map. -/
def IsSmooth (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) : Prop :=
  ∀ {U V : 𝒮.bigSite S}
    (a : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
    (b : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ Y) (h : U ⟶ V),
    relativelyEtale a → relativelyEtale b →
      a ≫ f = (𝒮.bigTopology S).sheafifiedRepresentableFunctor.map h ≫ b →
        AlgebraicGeometry.Smooth ((𝒮.bigToScheme S).map h)

/-- Smoothness is equivalent to smoothness of all scheme maps in relatively
étale squares of sheafified representables. -/
theorem isSmooth_iff (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) :
    IsSmooth 𝒮 S f ↔
      ∀ {U V : 𝒮.bigSite S}
        (a : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
        (b : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ Y) (h : U ⟶ V),
        relativelyEtale a → relativelyEtale b →
          a ≫ f = (𝒮.bigTopology S).sheafifiedRepresentableFunctor.map h ≫ b →
            AlgebraicGeometry.Smooth ((𝒮.bigToScheme S).map h) := Iff.rfl

end AlgebraicGeometry.ChosenBigFppfSite
