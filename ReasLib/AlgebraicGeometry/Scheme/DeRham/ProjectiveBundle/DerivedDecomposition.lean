module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open RingedSite.Hom
open AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
open scoped MonoidalCategory TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle

variable {S X P : Scheme.{u}}

/-- The source of the derived projective-bundle formula, indexed by the powers
`0, ..., r - 1` of `c₁ᵈᴿ(𝒪_P(1))`. -/
noncomputable abbrev derivedSource (f : X ⟶ S) (r : ℕ) :=
  LerayHirsch.overBaseSource f (fun t : Fin r ↦ 2 * (t : ℕ))

/-- The projective-bundle source is the finite biproduct of the shifts
`Ωᵈᴿ[X/S][-2t]`. -/
theorem derivedSource_def (f : X ⟶ S) (r : ℕ) :
    derivedSource f r =
      ⨁ fun t : Fin r ↦ (derivedComplex f)⟦-(2 * (t : ℕ) : ℤ)⟧ := sorry

/-- The derived direct image of the relative de Rham complex of the represented
projective bundle. -/
noncomputable abbrev derivedTarget (f : X ⟶ S) (π : P ⟶ X)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u}
        (Cohomology.coefficientHom (structureSquare f π)))
      (ModuleQis.{u}
        (RingedSpace.DeRham.coefficientSite (π ≫ f).toLRSHom.toShHom))] :=
  (modulePushforwardDerived.{u}
    (Cohomology.coefficientHom (structureSquare f π))).obj
      (derivedComplex (π ≫ f))

/-- The target is the derived pushforward of the projective bundle's relative de Rham
complex along the coefficient morphism of `structureSquare`. -/
theorem derivedTarget_def (f : X ⟶ S) (π : P ⟶ X)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u}
        (Cohomology.coefficientHom (structureSquare f π)))
      (ModuleQis.{u}
        (RingedSpace.DeRham.coefficientSite (π ≫ f).toLRSHom.toShHom))] :
    derivedTarget f π =
      (modulePushforwardDerived.{u}
        (Cohomology.coefficientHom (structureSquare f π))).obj
          (derivedComplex (π ≫ f)) := sorry

variable {E : X.Modules} (f : X ⟶ S) (E : X.Modules) (r : ℕ)
variable (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)

variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{u}
    (Cohomology.coefficientHom (structureSquare f π)))
  (ModuleQis.{u}
    (RingedSpace.DeRham.coefficientSite (π ≫ f).toLRSHom.toShHom))]

/-- The derived projective-bundle map obtained by specializing the absolute
Leray–Hirsch map to the powers of `c₁ᵈᴿ(𝒪_P(1))`. -/
noncomputable def derivedMap : derivedSource f r ⟶ derivedTarget f π :=
  LerayHirsch.overBaseMap (structureSquare f π)
    (fun t : Fin r ↦ 2 * (t : ℕ)) (fun t ↦ canonicalChernPower f π hπ t)

/-- The derived projective-bundle map is the corresponding specialization of
`LerayHirsch.overBaseMap`. -/
theorem derivedMap_def :
    derivedMap f E r π hπ =
      LerayHirsch.overBaseMap (structureSquare f π)
        (fun t : Fin r ↦ 2 * (t : ℕ)) (fun t ↦ canonicalChernPower f π hπ t) := sorry

/-- The inclusion of the `t`-th initial summand into the full `r`-summand index. -/
def initialIndex (t : Fin (r - 1)) : Fin r :=
  Fin.castLE (Nat.sub_le r 1) t

/-- The initial inclusion preserves the numerical index. -/
theorem initialIndex_val (t : Fin (r - 1)) : (initialIndex r t : ℕ) = t := sorry

/-- The source `K`, consisting of the summands indexed by `0, ..., r - 2`. -/
noncomputable abbrev initialSource :=
  ⨁ fun t : Fin (r - 1) ↦ (derivedComplex f)⟦-(2 * (t : ℕ) : ℤ)⟧

/-- The source `M`, represented as one additional `[-2]` shift on every summand of `K`. -/
noncomputable abbrev tailSource :=
  ⨁ fun t : Fin (r - 1) ↦
    ((derivedComplex f)⟦-(2 * (t : ℕ) : ℤ)⟧)⟦(-2 : ℤ)⟧

/-- The source `K` is the biproduct of the shifts indexed by `0, ..., r - 2`. -/
theorem initialSource_def : initialSource f r =
    ⨁ fun t : Fin (r - 1) ↦ (derivedComplex f)⟦-(2 * (t : ℕ) : ℤ)⟧ := sorry

/-- The source `M` is the biproduct of the positive summands, with the shift by
`-2(t+1)` expressed as successive shifts by `-2t` and `-2`. -/
theorem tailSource_def : tailSource f r =
    ⨁ fun t : Fin (r - 1) ↦
      ((derivedComplex f)⟦-(2 * (t : ℕ) : ℤ)⟧)⟦(-2 : ℤ)⟧ := sorry

/-- The positive-summand index corresponding to `t` is `t + 1`. -/
theorem tailIndex_isLt (t : Fin (r - 1)) : (t : ℕ) + 1 < r := sorry

/-- The inclusion of the positive index `t + 1` into the full `r`-summand index. -/
def tailIndex (t : Fin (r - 1)) : Fin r :=
  ⟨(t : ℕ) + 1, tailIndex_isLt r t⟩

/-- The positive inclusion has numerical value `t + 1`. -/
theorem tailIndex_val (t : Fin (r - 1)) : (tailIndex r t : ℕ) = (t : ℕ) + 1 := sorry

/-- The two-step shift indexing a tail summand has the degree of its corresponding
positive summand in `derivedSource`. -/
theorem tailDegree_eq (t : Fin (r - 1)) :
    -(2 * (t : ℕ) : ℤ) + (-2 : ℤ) =
      -(2 * (tailIndex r t : ℕ) : ℤ) := sorry

/-- The restriction of `derivedMap` to `K`. -/
noncomputable def initialMap : initialSource f r ⟶ derivedTarget f π :=
  biproduct.desc fun t ↦
    LerayHirsch.overBaseComponent (structureSquare f π)
      (fun i : Fin r ↦ 2 * (i : ℕ)) (fun i ↦ canonicalChernPower f π hπ i)
        (initialIndex r t)

/-- Each component of `initialMap` is the corresponding component of the derived
projective-bundle map. -/
theorem initialMap_ι (t : Fin (r - 1)) :
    biproduct.ι (fun j : Fin (r - 1) ↦
      (derivedComplex f)⟦-(2 * (j : ℕ) : ℤ)⟧) t ≫
        initialMap f E r π hπ =
      LerayHirsch.overBaseComponent (structureSquare f π)
        (fun i : Fin r ↦ 2 * (i : ℕ)) (fun i ↦ canonicalChernPower f π hπ i)
          (initialIndex r t) := sorry

/-- The canonical identification `K ≅ M[2]`, obtained componentwise from cancellation
of the consecutive shifts `[-2]` and `[2]` and from preservation of finite biproducts. -/
noncomputable def tailShiftIso : initialSource f r ≅ (tailSource f r)⟦(2 : ℤ)⟧ :=
  biproduct.mapIso (fun t : Fin (r - 1) ↦
      (shiftNegShift ((derivedComplex f)⟦-(2 * (t : ℕ) : ℤ)⟧) (2 : ℤ)).symm) ≪≫
    ((shiftFunctor _ (2 : ℤ)).mapBiproduct (fun t : Fin (r - 1) ↦
      ((derivedComplex f)⟦-(2 * (t : ℕ) : ℤ)⟧)⟦(-2 : ℤ)⟧)).symm

/-- On every summand, `tailShiftIso` is cancellation of `[-2]` followed by `[2]`,
then the inverse biproduct comparison for the shift functor. -/
theorem tailShiftIso_hom_ι (t : Fin (r - 1)) :
    biproduct.ι (fun j : Fin (r - 1) ↦
      (derivedComplex f)⟦-(2 * (j : ℕ) : ℤ)⟧) t ≫
        (tailShiftIso f r).hom =
      (shiftNegShift ((derivedComplex f)⟦-(2 * (t : ℕ) : ℤ)⟧) (2 : ℤ)).inv ≫
        (shiftFunctor _ (2 : ℤ)).map
          (biproduct.ι (fun j : Fin (r - 1) ↦
            ((derivedComplex f)⟦-(2 * (j : ℕ) : ℤ)⟧)⟦(-2 : ℤ)⟧) t) := sorry

/-- The restriction to the positive summands `M`, obtained from the restriction to `K`
by the pushed first-Chern action and the canonical source-shift equivalence. -/
noncomputable def tailMap : tailSource f r ⟶ derivedTarget f π :=
  ((shiftFunctor _ (-2 : ℤ)).mapBiproduct (fun t : Fin (r - 1) ↦
      (derivedComplex f)⟦-(2 * (t : ℕ) : ℤ)⟧)).inv ≫
    ShiftedHom.sourceShiftEquiv (initialSource f r) (derivedTarget f π) (2 : ℤ)
      (initialMap f E r π hπ ≫ canonicalPushedFirstChernMap f π hπ)

/-- The map `tailMap` is the shifted composite of the initial restriction with the
pushed first-Chern action. -/
theorem tailMap_def :
    tailMap f E r π hπ =
      ((shiftFunctor _ (-2 : ℤ)).mapBiproduct (fun t : Fin (r - 1) ↦
          (derivedComplex f)⟦-(2 * (t : ℕ) : ℤ)⟧)).inv ≫
        ShiftedHom.sourceShiftEquiv (initialSource f r) (derivedTarget f π) (2 : ℤ)
          (initialMap f E r π hπ ≫ canonicalPushedFirstChernMap f π hπ) := sorry

/-- Each component of `tailMap` is the corresponding positive component of
`derivedMap`, transported through the canonical shift comparison. -/
theorem tailMap_ι (t : Fin (r - 1)) :
    biproduct.ι (fun j : Fin (r - 1) ↦
      ((derivedComplex f)⟦-(2 * (j : ℕ) : ℤ)⟧)⟦(-2 : ℤ)⟧) t ≫
        tailMap f E r π hπ =
      ((shiftFunctorAdd' _ (-(2 * (t : ℕ) : ℤ)) (-2 : ℤ)
        (-(2 * (tailIndex r t : ℕ) : ℤ))
          (tailDegree_eq r t)).symm.app (derivedComplex f)).hom ≫
        biproduct.ι (fun i : Fin r ↦
          (derivedComplex f)⟦-(2 * (i : ℕ) : ℤ)⟧) (tailIndex r t) ≫
            derivedMap f E r π hπ := sorry

/-- Shifting the positive-summand restriction by two gives the restriction to `K`
followed by the pushed first-Chern action under the identification `K ≅ M[2]`. -/
theorem tailMap_shift :
    (shiftFunctor _ (2 : ℤ)).map (tailMap f E r π hπ) =
      (tailShiftIso f r).inv ≫ initialMap f E r π hπ ≫
        canonicalPushedFirstChernMap f π hπ := sorry

/-- The head/tail projective-bundle map with canonical pullback on the head and
`tailMap` on the positive summands. -/
noncomputable def headTailMap (hr : 0 < r) :
    derivedComplex f ⊞ tailSource f r ⟶ derivedTarget f π :=
  biprod.desc (Cohomology.derivedPullback (structureSquare f π))
    (tailMap f E r π hπ)

/-- The head component of `headTailMap` is the canonical derived pullback `c_{P/X}`. -/
theorem headTailMap_inl (hr : 0 < r) :
    biprod.inl ≫ headTailMap f E r π hπ hr =
      Cohomology.derivedPullback (structureSquare f π) := sorry

/-- The tail component of `headTailMap` is `tailMap`. -/
theorem headTailMap_inr (hr : 0 < r) :
    biprod.inr ≫ headTailMap f E r π hπ hr =
      tailMap f E r π hπ := sorry

-- Local instance justification (defeq pin): the shifted pullback/action formula uses the same canonical total-derived direct-image shift as its components.
attribute [local instance] AlgebraicGeometry.Scheme.DeRham.CanonicalTensor.pushforwardCommShift

/-- The derived projective-bundle map defined by the powers of
`c₁ᵈᴿ(𝒪_P(1))` is an isomorphism. -/
instance derivedMapIsIso [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] : IsIso (derivedMap f E r π hπ) := sorry

/-- The zeroth component of the projective-bundle map is the
canonical derived pullback `c_{P/X}`. -/
theorem derivedMap_ι_zero (hr : 0 < r) :
    biproduct.ι (fun t : Fin r ↦ (derivedComplex f)⟦-(2 * (t : ℕ) : ℤ)⟧)
        ⟨0, hr⟩ ≫ derivedMap f E r π hπ =
      ShiftedHom.sourceShiftEquiv (derivedComplex f) (derivedTarget f π) 0
        (ShiftedHom.mk₀ 0 rfl
          (Cohomology.derivedPullback (structureSquare f π))) := sorry

/-- On the `t`-th summand, the derived projective-bundle map is
shifted pullback followed by the pushed action of `c₁ᵈᴿ(𝒪_P(1)) ^ t`. -/
theorem derivedMap_ι_eq (t : Fin r) :
    biproduct.ι (fun i : Fin r ↦ (derivedComplex f)⟦-(2 * (i : ℕ) : ℤ)⟧) t ≫
        derivedMap f E r π hπ =
      ShiftedHom.sourceShiftEquiv (derivedComplex f) (derivedTarget f π)
        (2 * (t : ℕ) : ℤ)
        (Cohomology.derivedPullback (structureSquare f π) ≫
          (modulePushforwardDerived.{u}
            (Cohomology.coefficientHom (structureSquare f π))).shiftedHomMap
              (Iso.refl _) (Iso.refl _) (2 * (t : ℕ) : ℤ)
                (cast (congrArg (fun n : ℤ ↦
                  ShiftedHom (derivedComplex (π ≫ f)) (derivedComplex (π ≫ f)) n)
                    (chernMapDegree_eq t)) (canonicalChernMapPower f π hπ t))) := sorry

/-- The canonical pullback together with the restriction to the
positive summands is an isomorphism. -/
instance headTailMapIsIso [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (hr : 0 < r) :
    IsIso (headTailMap f E r π hπ hr) := sorry

/-- Multiplication by `c₁ᵈᴿ(𝒪_P(1))` intertwines the
restrictions to `K` and `M` under the canonical identification `K ≅ M[2]`. -/
theorem decompositionSquare (hr : 0 < r) :
    CommSq (tailShiftIso f r).hom (initialMap f E r π hπ)
      ((shiftFunctor _ (2 : ℤ)).map (tailMap f E r π hπ))
      (canonicalPushedFirstChernMap f π hπ) := sorry

end AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle
