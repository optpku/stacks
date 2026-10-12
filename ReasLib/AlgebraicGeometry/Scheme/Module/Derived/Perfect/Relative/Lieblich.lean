/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.FlatModel.Bounded
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative.FiniteType

/-!
# Bounded local models for relative perfectness

The Lieblich condition gives a local bounded model whose terms are flat over the base and
finitely presented over the source. For flat locally finitely presented morphisms, this
condition agrees with the standard and locally-finite-type notions of relative perfectness.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

variable {X S : Scheme.{u}}

/-- The local bounded-model condition for relative perfectness: locally on the source there is
a bounded complex of modules which are flat over the base and finitely presented over the
source, representing the given derived module up to isomorphism. -/
def lieblichPerfectOver (f : X ⟶ S) [LocallyOfFiniteType f] :
    ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace) :=
  fun E ↦
    ∃ 𝒰 : X.AffineOpenCover.{u}, ∀ i : 𝒰.I₀,
      ∃ P : Compᵇ((Spec (𝒰.X i)).toRingedSpace.Modules),
        (∀ n : ℤ, SheafOfModules.IsFlatOver (P.obj.X n) (𝒰.f i ≫ f).toShHom) ∧
          (∀ n : ℤ, (P.obj.X n).IsFinitePresentation) ∧
          IsIsomorphic
            (((RingedSpace.Hom.IsFlat.exactPullback (𝒰.f i).toShHom).mapDerivedCategory).obj E)
            (DerivedCategory.Q.obj P.obj)

/-- Object-level membership in the Lieblich local bounded-model condition. -/
abbrev IsLieblichPerfectOver (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) : Prop :=
  lieblichPerfectOver f E

/-- The Lieblich local-model condition unfolds to its affine cover, bounded representatives,
termwise relative flatness, finite presentation, and derived isomorphisms. -/
theorem lieblichPerfectOver_iff_affineOpenCover (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    IsLieblichPerfectOver f E ↔
      ∃ 𝒰 : X.AffineOpenCover.{u}, ∀ i : 𝒰.I₀,
        ∃ P : Compᵇ((Spec (𝒰.X i)).toRingedSpace.Modules),
          (∀ n : ℤ, SheafOfModules.IsFlatOver (P.obj.X n) (𝒰.f i ≫ f).toShHom) ∧
            (∀ n : ℤ, (P.obj.X n).IsFinitePresentation) ∧
            IsIsomorphic
              (((RingedSpace.Hom.IsFlat.exactPullback
                (𝒰.f i).toShHom).mapDerivedCategory).obj E)
              (DerivedCategory.Q.obj P.obj) := sorry

/-- The Lieblich local-model condition is invariant under isomorphisms of derived modules. -/
instance lieblichPerfectOver_isClosedUnderIsomorphisms (f : X ⟶ S)
    [LocallyOfFiniteType f] :
    (lieblichPerfectOver f).IsClosedUnderIsomorphisms := sorry

/-- For a flat, locally finitely presented morphism, relative perfectness agrees with the
Lieblich local bounded-model condition. -/
theorem isPerfectRelativeTo_iff_lieblichPerfectOver (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    IsPerfectRelativeTo f E ↔ IsLieblichPerfectOver f E := sorry

/-- For a flat, locally finitely presented morphism, relative perfectness defined using
relative pseudo-coherence agrees with the standard scheme-relative predicate. -/
theorem isPerfectOver_iff_isPerfectRelativeTo (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    IsPerfectOver f E ↔ IsPerfectRelativeTo f E := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
