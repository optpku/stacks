module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Henselian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap68.Lemma_68_18_10_Fibre
public import stacks_project.Chap71.Lemma_71_15_2_Fiber
public import stacks_project.Chap77.«77_7_1_1_BaseChange»

/-!
# Local flattening along a subset of a closed fibre

Over an affine henselian local base, flatness of a finite-type quasi-coherent module on an
algebraic space, along a subset of the closed fibre, is represented by a closed subscheme.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The condition that the base change of `ℱ` along `g : T ⟶ S` is flat over `T` at those
points of `|X_t|` whose image in `|X|` lies in the image of `E ⊆ Points (fiber f s)`. -/
def flatOverAlongFiberSubset {S : Scheme.{u}} {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) (ℱ : X.Modules) {T : Scheme.{u}}
    (g : T ⟶ S) (t : T) {s : S}
    (E : Set (Points (fiber f s))) : Prop :=
  let a := ofOverHomMk g (Category.comp_id g)
  ∀ x : Points (baseChangeSpace f a),
    x ∈ fiberOver (Limits.pullback.snd f a) (ofOver.pointsEquiv (Over.mk g) t) →
      Points.map (Limits.pullback.fst f a) x ∈ Points.map (fiberι f s) '' E →
        flatOverAt (baseChangeModule f a ℱ) (Limits.pullback.snd f a) x

/-- `flatOverAlongFiberSubset` unpacks as pointwise relative flatness on the set-theoretic
fibre of `X_T → T` at points mapping into `E`. -/
theorem flatOverAlongFiberSubset_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) (ℱ : X.Modules) {T : Scheme.{u}}
    (g : T ⟶ S) (t : T) {s : S}
    (E : Set (Points (fiber f s))) :
    flatOverAlongFiberSubset f ℱ g t E ↔
      let a := ofOverHomMk g (Category.comp_id g)
      ∀ x : Points (baseChangeSpace f a),
        x ∈ fiberOver (Limits.pullback.snd f a) (ofOver.pointsEquiv (Over.mk g) t) →
          Points.map (Limits.pullback.fst f a) x ∈ Points.map (fiberι f s) '' E →
            flatOverAt (baseChangeModule f a ℱ) (Limits.pullback.snd f a) x :=
  sorry

/-- Lemma 77.10.1 (1): over an affine henselian local base `S` with closed point `s`, a
locally finite-type morphism `f : X ⟶ ofOver (Over.mk (𝟙 S))` of algebraic spaces and a
finite-type quasi-coherent `ℱ : X.Modules`, any subset `E ⊆ Points (fiber f s)` is
represented by a closed subscheme `Z` of `S`: for pointed scheme maps `g : T ⟶ S` with
`g t = s`, `flatOverAlongFiberSubset f ℱ g t E` if and only if
`Over.mk (T.fromSpecStalk t ≫ g)` factors through `Z`. -/
@[stacks 0CWP]
theorem exists_closedImmersion_over_subset {S : Scheme.{u}} [IsAffine S]
    [HenselianLocalRing Γ(S, ⊤)] {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (s : S) (hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤))
    (E : Set (Points (fiber f s))) :
    ∃ Z : Over S, AlgebraicGeometry.IsClosedImmersion Z.hom ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S) (t : T) (ht : g t = s),
        flatOverAlongFiberSubset f ℱ g t E ↔
          Nonempty (Over.mk (T.fromSpecStalk t ≫ g) ⟶ Z) :=
  sorry

/-- Lemma 77.10.1 (2): if moreover `f` is locally of finite presentation, `ℱ` is of finite
presentation, and `E ⊆ Points (fiber f s)` is closed and quasi-compact, then the representing
closed subscheme `Z ⟶ S` may be taken of finite presentation. -/
@[stacks 0CWP]
theorem exists_closedImmersion_over_subset_of_finitePresentation {S : Scheme.{u}}
    [IsAffine S] [HenselianLocalRing Γ(S, ⊤)] {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) [LocallyOfFinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    (s : S) (hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤))
    (E : Set (Points (fiber f s))) (hE_closed : IsClosed E) (hE_compact : IsCompact E) :
    ∃ Z : Over S,
      (AlgebraicGeometry.IsClosedImmersion Z.hom ∧ Scheme.Hom.FinitePresentation Z.hom) ∧
        ∀ {T : Scheme.{u}} (g : T ⟶ S) (t : T) (ht : g t = s),
          flatOverAlongFiberSubset f ℱ g t E ↔
            Nonempty (Over.mk (T.fromSpecStalk t ≫ g) ⟶ Z) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
