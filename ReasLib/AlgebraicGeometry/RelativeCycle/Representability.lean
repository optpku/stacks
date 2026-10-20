/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import ReasLib.AlgebraicGeometry.RelativeCycle.Functor
public import ReasLib.AlgebraicGeometry.RelativeCycle.Reduction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Presentation
public import ReasLib.CategoryTheory.Sites.Sheafification.Map

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- The big `h` topology restricted to schemes locally of finite type over `S`. -/
def locallyOfFiniteTypeOverHTopology (S : Scheme.{u}) :
    GrothendieckTopology (LocallyOfFiniteTypeOver S) :=
  (MorphismProperty.Over.forget (@LocallyOfFiniteType) ⊤ S).restrictedTopology
    ((Scheme.hPrecoverage.toGrothendieck).over S)

/-- There exist a locally Noetherian base, a locally finite type morphism, and a
nonnegative dimension for which the effective relative-cycle presheaf is not representable. -/
theorem effectiveFunctor_not_isRepresentable :
    ∃ (X S : Scheme.{u}) (f : X ⟶ S) (_ : IsLocallyNoetherian S)
      (_ : LocallyOfFiniteType f) (r : ℕ),
      ¬ (effectiveFunctor f r).IsRepresentable :=
  sorry

/-- For a projective morphism over a locally Noetherian Nagata scheme over the rational
numbers, the effective relative-cycle presheaf on seminormal test schemes is representable. -/
instance effectiveFunctorSeminormal_isRepresentable {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    [S.Over (Spec (CommRingCat.of (ULift.{u} ℚ)))] [Scheme.Nagata S] [Projective f]
    (r : ℕ) :
    (effectiveFunctorSeminormal f r).IsRepresentable :=
  sorry

/-- For a projective morphism over a locally Noetherian base, the effective relative-cycle
presheaf and a representable presheaf admit a common sheafification for the restricted h topology. -/
theorem exists_isRepresentable_hSheafification_iso {X S : Scheme.{u}}
    (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f] [Projective f]
    (r : ℕ) :
    ∃ (G H : (LocallyOfFiniteTypeOver S)ᵒᵖ ⥤ Type u)
      (η : effectiveFunctor f r ⟶ H) (θ : G ⟶ H),
        G.IsRepresentable ∧
          Presheaf.IsSheafification (locallyOfFiniteTypeOverHTopology S) η ∧
          Presheaf.IsSheafification (locallyOfFiniteTypeOverHTopology S) θ :=
  sorry


end AlgebraicGeometry.RelativeCycle
