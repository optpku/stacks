module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap75.Lemma_75_26_6_RankLocus

/-!
# Relative pseudo-coherence on algebraic spaces

An object of `D(𝒪_X)` is `m`-pseudo-coherent relative to `Y` when every étale
affine scheme chart square over `f : X ⟶ Y` satisfies the closed-immersion
criterion into a finite-dimensional affine space over the target chart.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- On an affine finite type morphism, relative `m`-pseudo-coherence means that some
closed immersion into a finite-dimensional affine space over the base has
`m`-pseudo-coherent derived pushforward. -/
def IsMPseudoCoherentOverAffine {X S : Scheme.{u}} (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ) : Prop :=
  ∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S),
    AlgebraicGeometry.IsClosedImmersion i ∧
      i ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = f ∧
      RingedSpace.ModuleDerived.IsMPseudoCoherent
        ((RingedSpace.moduleDerivedPushforward i.toShHom).obj E) m

/-- The affine relative `m`-pseudo-coherence predicate is exactly its affine-space
pushforward criterion. -/
theorem isMPseudoCoherentOverAffine_iff {X S : Scheme.{u}} (f : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ) :
    IsMPseudoCoherentOverAffine f E m ↔
      ∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S),
        AlgebraicGeometry.IsClosedImmersion i ∧
          i ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = f ∧
          RingedSpace.ModuleDerived.IsMPseudoCoherent
            ((RingedSpace.moduleDerivedPushforward i.toShHom).obj E) m :=
  sorry

/-- An object `E` of `D(𝒪_X)` is `m`-pseudo-coherent relative to `Y` if, on every
étale affine scheme chart square over `f`, the derived restriction of `E` to the
source chart satisfies the affine-space relative `m`-pseudo-coherence criterion. -/
def IsMPseudoCoherentOver {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (E : ModuleDerived X) (m : ℤ) : Prop :=
  ∀ (U V : Over S) [IsAffine U.left] [IsAffine V.left] (φ : ofOver U ⟶ X)
    (ψ : ofOver V ⟶ Y) (h : U ⟶ V) [AlgebraicSpace.Etale φ]
    [AlgebraicSpace.Etale ψ] [AlgebraicGeometry.LocallyOfFiniteType h.left],
    φ ≫ f = ofOverMap h ≫ ψ →
      IsMPseudoCoherentOverAffine h.left
        (Eq.mp (derivedCategory_modules_eq_ringedSpace U.left)
          ((restrictToSchemeDerived U).obj ((pullback φ).obj E))) m

/-- Relative `m`-pseudo-coherence on algebraic spaces unfolds to the étale affine
scheme chart criterion. -/
theorem isMPseudoCoherentOver_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (E : ModuleDerived X) (m : ℤ) :
    IsMPseudoCoherentOver f E m ↔
      ∀ (U V : Over S) [IsAffine U.left] [IsAffine V.left] (φ : ofOver U ⟶ X)
        (ψ : ofOver V ⟶ Y) (h : U ⟶ V) [AlgebraicSpace.Etale φ]
        [AlgebraicSpace.Etale ψ] [AlgebraicGeometry.LocallyOfFiniteType h.left],
        φ ≫ f = ofOverMap h ≫ ψ →
          IsMPseudoCoherentOverAffine h.left
            (Eq.mp (derivedCategory_modules_eq_ringedSpace U.left)
              ((restrictToSchemeDerived U).obj ((pullback φ).obj E))) m :=
  sorry

/-- On an étale affine scheme chart square, relative `m`-pseudo-coherence of `E`
over `Y` restricts to the affine-space criterion on the source chart. -/
theorem isMPseudoCoherentOver_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {E : ModuleDerived X} {m : ℤ}
    (hE : IsMPseudoCoherentOver f E m) {U V : Over S} [IsAffine U.left]
    [IsAffine V.left] (φ : ofOver U ⟶ X) (ψ : ofOver V ⟶ Y) (h : U ⟶ V)
    [AlgebraicSpace.Etale φ] [AlgebraicSpace.Etale ψ]
    [AlgebraicGeometry.LocallyOfFiniteType h.left]
    (w : φ ≫ f = ofOverMap h ≫ ψ) :
    IsMPseudoCoherentOverAffine h.left
      (Eq.mp (derivedCategory_modules_eq_ringedSpace U.left)
        ((restrictToSchemeDerived U).obj ((pullback φ).obj E))) m :=
  sorry

/-- An object `E` of `D(𝒪_X)` is pseudo-coherent relative to `Y` if it is
`m`-pseudo-coherent relative to `Y` for every integer `m`. -/
def IsPseudoCoherentOver {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (E : ModuleDerived X) : Prop :=
  ∀ m : ℤ, IsMPseudoCoherentOver f E m

/-- Relative pseudo-coherence on algebraic spaces is equivalent to relative
`m`-pseudo-coherence in every degree. -/
theorem isPseudoCoherentOver_iff_forall_mPseudoCoherentOver {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (E : ModuleDerived X) :
    IsPseudoCoherentOver f E ↔ ∀ m : ℤ, IsMPseudoCoherentOver f E m :=
  sorry

/-- Relative pseudo-coherence on algebraic spaces unfolds to the affine-space
criterion on every étale affine scheme chart square, in every degree. -/
theorem isPseudoCoherentOver_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (E : ModuleDerived X) :
    IsPseudoCoherentOver f E ↔
      ∀ (U V : Over S) [IsAffine U.left] [IsAffine V.left] (φ : ofOver U ⟶ X)
        (ψ : ofOver V ⟶ Y) (h : U ⟶ V) [AlgebraicSpace.Etale φ]
        [AlgebraicSpace.Etale ψ] [AlgebraicGeometry.LocallyOfFiniteType h.left],
        φ ≫ f = ofOverMap h ≫ ψ →
          ∀ m : ℤ, IsMPseudoCoherentOverAffine h.left
            (Eq.mp (derivedCategory_modules_eq_ringedSpace U.left)
              ((restrictToSchemeDerived U).obj ((pullback φ).obj E))) m :=
  sorry

/-- On an étale affine scheme chart square, relative pseudo-coherence of `E` over
`Y` restricts to the affine-space criterion in every degree. -/
theorem isPseudoCoherentOver_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {E : ModuleDerived X}
    (hE : IsPseudoCoherentOver f E) {U V : Over S} [IsAffine U.left]
    [IsAffine V.left] (φ : ofOver U ⟶ X) (ψ : ofOver V ⟶ Y) (h : U ⟶ V)
    [AlgebraicSpace.Etale φ] [AlgebraicSpace.Etale ψ]
    [AlgebraicGeometry.LocallyOfFiniteType h.left]
    (w : φ ≫ f = ofOverMap h ≫ ψ) :
    ∀ m : ℤ, IsMPseudoCoherentOverAffine h.left
      (Eq.mp (derivedCategory_modules_eq_ringedSpace U.left)
        ((restrictToSchemeDerived U).obj ((pullback φ).obj E))) m :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
