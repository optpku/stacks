module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Henselian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.Point
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.Map
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

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

/-- Over an affine henselian local base `S` with closed point `s`, a
locally finite-type morphism `f : X ⟶ ofOver (Over.mk (𝟙 S))` of algebraic spaces and a
finite-type quasi-coherent `ℱ : X.Modules`, any subset `E ⊆ Points (fiber f s)` is
represented by a closed subscheme `Z` of `S`: for pointed scheme maps `g : T ⟶ S` with
`g t = s`, `flatOverAlongFiberSubset f ℱ g t E` if and only if
`Over.mk (T.fromSpecStalk t ≫ g)` factors through `Z`. -/
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

/-- Over an affine henselian local base, a finitely presented module on a locally
finitely presented algebraic space admits a finitely presented closed subscheme representing
flatness along a closed quasi-compact subset of the closed fibre. -/
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
