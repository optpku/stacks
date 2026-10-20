/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

#check (FormallyEtale : {X S : Scheme.{u}} → (X ⟶ S) → Prop)

#check (Scheme.Hom.formallyEtale_appLE :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [FormallyEtale f]
    {U : S.Opens}, IsAffineOpen U → ∀ {V : X.Opens}, IsAffineOpen V →
      ∀ e : V ≤ f ⁻¹ᵁ U, (f.appLE U V e).hom.FormallyEtale)

#check (FormallyEtale.instHasRingHomProperty :
  HasRingHomProperty (@FormallyEtale.{u}) RingHom.FormallyEtale)

#check (FormallyEtale.instIsStableUnderComposition :
  MorphismProperty.IsStableUnderComposition (@FormallyEtale.{u}))

#check (FormallyEtale.instIsMultiplicative :
  MorphismProperty.IsMultiplicative (@FormallyEtale.{u}))

#check (FormallyEtale.instIsStableUnderBaseChange :
  MorphismProperty.IsStableUnderBaseChange (@FormallyEtale.{u}))

#check (FormallyEtale.toFormallyUnramified :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [FormallyEtale f], FormallyUnramified f)

#check (FormallyEtale.iff_existsUnique_lift :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    FormallyEtale f ↔
      ∀ {T T' : Scheme.{u}} [IsAffine T] [IsAffine T'] (i : T ⟶ T')
        [IsClosedImmersion i], i.ker ^ 2 = ⊥ → ∀ (g : T ⟶ X) (h : T' ⟶ S)
          (sq : CommSq g i f h), Nonempty (Unique sq.LiftStruct))

#check (FormallyEtale.existsUnique_lift :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [FormallyEtale f]
    {T T' : Scheme.{u}} [IsAffine T] [IsAffine T'] (i : T ⟶ T')
      [IsClosedImmersion i], i.ker ^ 2 = ⊥ → ∀ (g : T ⟶ X) (h : T' ⟶ S)
        (sq : CommSq g i f h), Nonempty (Unique sq.LiftStruct))

#check (FormallyEtale.of_existsUnique_lift :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    (∀ {T T' : Scheme.{u}} [IsAffine T] [IsAffine T'] (i : T ⟶ T')
      [IsClosedImmersion i], i.ker ^ 2 = ⊥ → ∀ (g : T ⟶ X) (h : T' ⟶ S)
        (sq : CommSq g i f h), Nonempty (Unique sq.LiftStruct)) → FormallyEtale f)

end AlgebraicGeometry
