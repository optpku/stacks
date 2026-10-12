/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.AffineSpace
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact

/-!
# Relative pseudo-coherence on schemes

Relative pseudo-coherence is tested on compatible affine covers by embedding each affine
piece into a finite-dimensional affine space over the corresponding affine base.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

variable {X S : Scheme.{u}}

/-- On an affine finite type morphism, relative `m`-pseudo-coherence means that some closed
immersion into a finite-dimensional affine space over the base has `m`-pseudo-coherent
derived pushforward. -/
def mPseudoCoherentOverAffine {A B : CommRingCat.{u}} (g : Spec A ⟶ Spec B)
    (h_finiteType : (Scheme.Hom.appTop g).hom.FiniteType) (m : ℤ) :
    ObjectProperty (RingedSpace.ModuleDerived (Spec A).toRingedSpace) :=
  fun E ↦
    ∃ (n : ℕ) (i : Spec A ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec B)),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace (ULift.{u} (Fin n)) (Spec B) ↘ Spec B) = g ∧
        RingedSpace.ModuleDerived.IsMPseudoCoherent
          ((RingedSpace.moduleDerivedPushforward i.toShHom).obj E) m

/-- The affine relative `m`-pseudo-coherence predicate is exactly its affine-space
pushforward criterion. -/
theorem mPseudoCoherentOverAffine_iff {A B : CommRingCat.{u}} (g : Spec A ⟶ Spec B)
    (h_finiteType : (Scheme.Hom.appTop g).hom.FiniteType) (m : ℤ)
    (E : RingedSpace.ModuleDerived (Spec A).toRingedSpace) :
    mPseudoCoherentOverAffine g h_finiteType m E ↔
      ∃ (n : ℕ) (i : Spec A ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec B)),
        IsClosedImmersion i ∧
          i ≫ (AffineSpace (ULift.{u} (Fin n)) (Spec B) ↘ Spec B) = g ∧
          RingedSpace.ModuleDerived.IsMPseudoCoherent
            ((RingedSpace.moduleDerivedPushforward i.toShHom).obj E) m := sorry

/-- Relative `m`-pseudo-coherence over a locally finite type scheme morphism, tested on
compatible affine covers of the target and source. -/
def mPseudoCoherentOver (f : X ⟶ S) [LocallyOfFiniteType f] (m : ℤ) :
    ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace) :=
  fun E ↦
    ∃ 𝒱 : S.AffineOpenCover.{u}, ∀ j : 𝒱.I₀,
      ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover.{u}, ∀ i : 𝒰.I₀,
        ∃ h_finiteType :
            (Scheme.Hom.appTop (𝒰.f i ≫ 𝒱.openCover.pullbackHom f j)).hom.FiniteType,
          mPseudoCoherentOverAffine
            (𝒰.f i ≫ 𝒱.openCover.pullbackHom f j) h_finiteType m
            (((RingedSpace.Hom.IsFlat.exactPullback
              (𝒰.f i ≫ (𝒱.openCover.pullback₁ f).f j).toShHom).mapDerivedCategory).obj E)

/-- Object-level membership in relative `m`-pseudo-coherence over a scheme morphism. -/
abbrev IsMPseudoCoherentOver (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ) : Prop :=
  mPseudoCoherentOver f m E

/-- Relative `m`-pseudo-coherence is exactly its compatible affine-cover criterion. -/
theorem mPseudoCoherentOver_iff_affineOpenCover (f : X ⟶ S)
    [LocallyOfFiniteType f] (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ) :
    IsMPseudoCoherentOver f E m ↔
      ∃ 𝒱 : S.AffineOpenCover.{u}, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover.{u}, ∀ i : 𝒰.I₀,
          ∃ h_finiteType :
              (Scheme.Hom.appTop (𝒰.f i ≫ 𝒱.openCover.pullbackHom f j)).hom.FiniteType,
            mPseudoCoherentOverAffine
              (𝒰.f i ≫ 𝒱.openCover.pullbackHom f j) h_finiteType m
              (((RingedSpace.Hom.IsFlat.exactPullback
                (𝒰.f i ≫ (𝒱.openCover.pullback₁ f).f j).toShHom).mapDerivedCategory).obj E) := sorry

/-- Relative pseudo-coherence over a locally finite type morphism means relative
`m`-pseudo-coherence for every integer `m`. -/
def pseudoCoherentOver (f : X ⟶ S) [LocallyOfFiniteType f] :
    ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace) :=
  fun E ↦ ∀ m : ℤ, IsMPseudoCoherentOver f E m

/-- Object-level membership in relative pseudo-coherence over a scheme morphism. -/
abbrev IsPseudoCoherentOver (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) : Prop :=
  pseudoCoherentOver f E

/-- Relative pseudo-coherence is equivalent to relative `m`-pseudo-coherence in every degree. -/
theorem pseudoCoherentOver_iff_forall_mPseudoCoherentOver (f : X ⟶ S)
    [LocallyOfFiniteType f] (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    IsPseudoCoherentOver f E ↔ ∀ m : ℤ, IsMPseudoCoherentOver f E m := sorry

/-- Relative pseudo-coherence is invariant under isomorphisms of derived modules. -/
instance pseudoCoherentOver_isClosedUnderIsomorphisms (f : X ⟶ S)
    [LocallyOfFiniteType f] :
    (pseudoCoherentOver f).IsClosedUnderIsomorphisms := sorry

/-- Relatively pseudo-coherent derived modules form a triangulated object property. -/
instance pseudoCoherentOver_isTriangulated (f : X ⟶ S) [LocallyOfFiniteType f] :
    (pseudoCoherentOver f).IsTriangulated := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
