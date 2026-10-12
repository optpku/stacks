/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Definition_42_50_3_LocalizedClasses
public import stacks_project.Chap42.Lemma_42_52_1
public import stacks_project.Chap42.Lemma_42_46_7
public import stacks_project.Chap42.Lemma_42_46_7_MorphismRepresentative

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open RingedSpace.ModuleDerived.Morphism

variable {S : Scheme.{u}} [UniversallyCatenary S]
variable {δ : S → ℤ} [IsDimensionFunction δ]
variable {X : Over S} [LocallyOfFiniteType X.hom]
variable {Z : Scheme.{u}}
variable (i : Z ⟶ X.left) [IsClosedImmersion i]
variable (T : Triangle (RingedSpace.ModuleDerived X.left.toRingedSpace))
variable (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.left.toRingedSpace))
variable (h1 : RingedSpace.ModuleDerived.IsPerfect T.obj₁)
variable (h2 : RingedSpace.ModuleDerived.IsPerfect T.obj₂)
variable (h3 : RingedSpace.ModuleDerived.IsPerfect T.obj₃)
variable (vanishing1 : IsZero (restrictAway i T.obj₁))
variable (vanishing3 : IsZero (restrictAway i T.obj₃))
variable (hfin :
    (∃ (Y : Scheme.{u}) (f : Y ⟶ X.left),
        IsEnvelope f ∧
          HasLocallyBoundedFiniteLocallyFree
            ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₃)) ∨
      HasLocallyBoundedFiniteLocallyFree T.mor₃ ∨
      (∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left)) ∨
      CompactSpace X.left)

include hT vanishing1 vanishing3

/-- The restrictions of `T.obj₁` and `T.obj₃` away from `Z` vanish, so the
restriction of `T.obj₂` also vanishes on the complement of `Z`. -/
theorem restrictAway_obj₂_isZero : IsZero (restrictAway i T.obj₂) := sorry

include h1 h2 h3 hfin

/-- Lemma 42.52.5 (1): in Situation 42.7.1, for `X` locally of finite type over `S`
and a closed immersion `Z ⟶ X`, a distinguished triangle of perfect objects of
`D(O_X)` with `T.obj₁` and `T.obj₃` vanishing on the complement of `Z`, and at
least one of the four connecting-map alternatives on `T.mor₃`, the localized
Newton classes add. -/
@[stacks 0FBE]
theorem newtonClass_distinguished
    (classes : ChernClass.Theory δ X.hom)
    (finiteness1 : TechnicalCondition X T.obj₁)
    (finiteness2 : TechnicalCondition X T.obj₂)
    (finiteness3 : TechnicalCondition X T.obj₃)
    (p : ℕ) :
    newtonClass i classes T.obj₂ h2
        (restrictAway_obj₂_isZero i T hT vanishing1 vanishing3) finiteness2 p =
      newtonClass i classes T.obj₁ h1 vanishing1 finiteness1 p +
        newtonClass i classes T.obj₃ h3 vanishing3 finiteness3 p := sorry

/-- Lemma 42.52.5 (2): under the same hypotheses, the localized Chern characters add. -/
@[stacks 0FBE]
theorem character_distinguished
    (classes : ChernClass.Theory δ X.hom)
    (finiteness1 : TechnicalCondition X T.obj₁)
    (finiteness2 : TechnicalCondition X T.obj₂)
    (finiteness3 : TechnicalCondition X T.obj₃) :
    character i classes T.obj₂ h2
        (restrictAway_obj₂_isZero i T hT vanishing1 vanishing3) finiteness2 =
      fun p ↦ character i classes T.obj₁ h1 vanishing1 finiteness1 p +
        character i classes T.obj₃ h3 vanishing3 finiteness3 p := sorry

end AlgebraicGeometry.LocalizedChern
