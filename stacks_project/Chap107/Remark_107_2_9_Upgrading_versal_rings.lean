module

public import ReasLib.RingTheory.Regular.GRing
public import ReasLib.RingTheory.Smooth.Adic.Basic
public import stacks_project.Chap98.Lemma_98_12_3_Associated
public import stacks_project.Chap98.Lemma_98_13_8_SmoothYoneda
public import stacks_project.Chap107.Definition_107_4_1_FormalBranches
public import stacks_project.Chap107.Lemma_107_2_3
public import stacks_project.Chap107.Lemma_107_2_5_Residue
public import stacks_project.Chap107.Lemma_107_2_6_Restrict
public import stacks_project.Chap107.Remark_107_2_9_Upgrading_versal_rings_Morphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Upgrading versal rings to morphisms `Spec(A) ⟶ X`

In Situation 107.2.1, Artin's axioms supply a morphism `Spec(A) ⟶ X` from a
versal ring, and the comparisons of Lemmas 107.2.4, 107.2.5, 107.2.6, and
107.2.8 may be chosen compatible with these morphisms up to a noncanonical
2-arrow. Implied power-series maps are well-defined up to formal homotopy.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open FiberedCategoryOver.Groupoids
open GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.CompleteLocalSAlgebra.Hom

variable {S : Scheme.{u}}

/-- Transport a morphism of complete local `S`-algebras along equalities of
source and target. -/
def congr {R R' T T' : CompleteLocalSAlgebra S} (hR : R = R') (hT : T = T')
    (φ : Hom R T) : Hom R' T' :=
  hR ▸ hT ▸ φ

/-- `congr` is substitution of equal source and target algebras. -/
theorem congr_eq {R R' T T' : CompleteLocalSAlgebra S} (hR : R = R')
    (hT : T = T') (φ : Hom R T) : congr hR hT φ = hR ▸ hT ▸ φ :=
  sorry

end AlgebraicGeometry.CompleteLocalSAlgebra.Hom

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}

/-- Remark 107.2.9 (Upgrading versal rings) (1): In Situation 107.2.1 let
`x0 : Spec(k) ⟶ X` be a morphism, where `k` is a finite type field over `S`.
Let `A` be a versal ring to `X` at `x0`. By Artin's Axioms, Lemma 98.9.5, the
versal formal object comes from a morphism `Spec(A) ⟶ X` over `S`. -/
@[stacks 0DR1]
theorem exists_realizesVersalRing [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A] :
    ∃ x : CompleteLocalObject X, RealizesVersalRing x0 A x :=
  sorry

/-- Remark 107.2.9 (Upgrading versal rings) (2): In Situation 107.2.1, the
isomorphism `A ≅ A'[[t₁, …, tᵣ]]` or `A' ≅ A[[t₁, …, tᵣ]]` of Lemma 107.2.4
may be chosen compatible with the morphisms `Spec(A) ⟶ X` and `Spec(A') ⟶ X`.
-/
@[stacks 0DR1]
theorem exists_isPowerSeriesExtension_compatible [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A A' : CompleteLocalSAlgebra S) [IsVersalRing x0 A] [IsVersalRing x0 A'] :
    (∃ (φ : CompleteLocalSAlgebra.Hom A A'),
        IsPowerSeriesExtension φ ∧
          ∃ x x' : CompleteLocalObject X,
            RealizesVersalRing x0 A x ∧ RealizesVersalRing x0 A' x' ∧
              ∃ (hA : ((approximation X).obj x).base = A)
                (hA' : ((approximation X).obj x').base = A')
                (f : GroupoidsOver.FormalObject.Hom ((approximation X).obj x)
                  ((approximation X).obj x')),
                CompleteLocalSAlgebra.Hom.congr hA hA' f.base = φ) ∨
      ∃ (φ : CompleteLocalSAlgebra.Hom A' A),
        IsPowerSeriesExtension φ ∧
          ∃ x x' : CompleteLocalObject X,
            RealizesVersalRing x0 A x ∧ RealizesVersalRing x0 A' x' ∧
              ∃ (hA : ((approximation X).obj x).base = A)
                (hA' : ((approximation X).obj x').base = A')
                (f : GroupoidsOver.FormalObject.Hom ((approximation X).obj x')
                  ((approximation X).obj x)),
                CompleteLocalSAlgebra.Hom.congr hA' hA f.base = φ :=
  sorry

/-- Remark 107.2.9 (Upgrading versal rings) (3): In Situation 107.2.1, the
homomorphism `A → A'` of Lemma 107.2.5 may be chosen compatible with the
morphisms `Spec(A) ⟶ X` and `Spec(A') ⟶ X`. -/
@[stacks 0DR1]
theorem exists_isVersalRing_restrict_compatible [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (l : Type u) [Field l] [Algebra x0.K l] [Module.Finite x0.K l]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A] :
    ∃ A' : CompleteLocalSAlgebra S,
      IsVersalRing (x0.restrict l) A' ∧
        ∃ φ : CompleteLocalSAlgebra.Hom A' A,
          φ.hom.formally_smooth_for_adic (maximalIdeal A'.carrier) ∧
            φ.InducesResidueExtension x0.K l x0.structureHom
                (x0.restrict l).structureHom ∧
              ∃ x x' : CompleteLocalObject X,
                RealizesVersalRing x0 A x ∧
                  RealizesVersalRing (x0.restrict l) A' x' ∧
                    ∃ (hA : ((approximation X).obj x).base = A)
                      (hA' : ((approximation X).obj x').base = A')
                      (f : GroupoidsOver.FormalObject.Hom
                        ((approximation X).obj x') ((approximation X).obj x)),
                      CompleteLocalSAlgebra.Hom.congr hA' hA f.base = φ :=
  sorry

/-- Remark 107.2.9 (Upgrading versal rings) (4): In Situation 107.2.1, if `x` is
versal at a finite type point `u0`, then the morphism
`Spec(O_{U, u0}^∧) ⟶ X` of Lemma 107.2.6 is the composition of the canonical
map `Spec(O_{U, u0}^∧) ⟶ U` and the given map `U ⟶ X`. -/
@[stacks 0DR1]
theorem realizesVersalRing_completeLocalObject [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    {U : Scheme.{u}} (hU : U ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    [IsVersalAt hU x hx u0] :
    RealizesVersalRing (FieldValuedPoint.induced hU x hx u0)
      (completionSAlgebra hU u0) (completeLocalObject hU x hx u0) :=
  sorry

/-- The 2-Yoneda 1-morphism of `completeLocalObject` is the composition of
`overMap` of `fromSpecCompletionOverHom` with `yonedaOfObject`. -/
theorem yonedaOfObject_completeLocalObject {U : Scheme.{u}} (hU : U ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0] :
    yonedaOfObject (completeLocalObject hU x hx u0).base.toS
        (completeLocalObject hU x hx u0).object
        (completeLocalObject hU x hx u0).over_obj =
      overMap (fromSpecCompletionOverHom hU u0) ≫ yonedaOfObject hU x hx :=
  sorry

/-- Remark 107.2.9 (Upgrading versal rings) (5): In Situation 107.2.1, if
`O_{S,s}` is a G-ring, then the isomorphism `O_{U, u0}^∧ ≅ A` of Lemma 107.2.8
may be chosen so that `Spec(A) ⟶ X` corresponds to the canonical completed-stalk
map `Spec(O_{U, u0}^∧) ⟶ U ⟶ X`. -/
@[stacks 0DR1]
theorem exists_smooth_realizesVersalRing [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A] (s : S)
    (hs : x0.structureHom (closedPoint x0.K) = s)
    [IsGRing (S.presheaf.stalk s)] :
    ∃ (W : SmoothFiniteTypeObject x0.structureHom x0.fiberObj)
      (φ : CompleteLocalSAlgebra.Hom A (completionSAlgebra W.toS W.u0)),
      Function.Bijective φ.hom ∧
        ∃ xA : CompleteLocalObject X,
          RealizesVersalRing x0 A xA ∧
            ∃ (hA : ((approximation X).obj xA).base = A)
              (hC :
                (associatedFormalObject W.toS W.object W.over_obj W.u0).base =
                  completionSAlgebra W.toS W.u0)
              (f : GroupoidsOver.FormalObject.Hom ((approximation X).obj xA)
                (associatedFormalObject W.toS W.object W.over_obj W.u0)),
              CompleteLocalSAlgebra.Hom.congr hA hC f.base = φ :=
  sorry

/-- Remark 107.2.9 (Upgrading versal rings) (6): In Situation 107.2.1, an implied
map `A' → A` or `A → A'` in Lemma 107.2.4 is well-defined up to formal homotopy,
see Formal Deformation Theory, Lemma 90.28.3. -/
@[stacks 0DR1]
theorem impliedHom_formallyHomotopic [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A A' : CompleteLocalSAlgebra S) [IsVersalRing x0 A] [IsVersalRing x0 A']
    {R T : CompleteLocalSAlgebra S}
    (hRT : (R = A ∧ T = A') ∨ (R = A' ∧ T = A))
    (φ ψ : CompleteLocalSAlgebra.Hom R T)
    (hφ : IsPowerSeriesExtension φ) (hψ : IsPowerSeriesExtension ψ)
    {x x' y y' : CompleteLocalObject X}
    (hx : RealizesVersalRing x0 R x) (hx' : RealizesVersalRing x0 T x')
    (hy : RealizesVersalRing x0 R y) (hy' : RealizesVersalRing x0 T y')
    (hRx : ((approximation X).obj x).base = R)
    (hTx : ((approximation X).obj x').base = T)
    (hRy : ((approximation X).obj y).base = R)
    (hTy : ((approximation X).obj y').base = T)
    (f : GroupoidsOver.FormalObject.Hom ((approximation X).obj x)
      ((approximation X).obj x'))
    (g : GroupoidsOver.FormalObject.Hom ((approximation X).obj y)
      ((approximation X).obj y'))
    (hf : CompleteLocalSAlgebra.Hom.congr hRx hTx f.base = φ)
    (hg : CompleteLocalSAlgebra.Hom.congr hRy hTy g.base = ψ) :
    FormallyHomotopic φ ψ :=
  sorry

end AlgebraicGeometry.AlgebraicStack
