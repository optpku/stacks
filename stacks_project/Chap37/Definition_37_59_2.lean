/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Module
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Definition 37.59.2 (1): an object of `D(𝒪_X)` is relatively `m`-pseudo-coherent
exactly when it satisfies the compatible affine-open-cover criterion. -/
@[stacks 09UI] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.mPseudoCoherentOver_iff_affineOpenCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ),
      Scheme.ModuleDerived.IsMPseudoCoherentOver f E m ↔
        ∃ 𝒱 : S.AffineOpenCover.{u}, ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover.{u}, ∀ i : 𝒰.I₀,
            ∃ h_finiteType :
                (Scheme.Hom.appTop
                  (𝒰.f i ≫ 𝒱.openCover.pullbackHom f j)).hom.FiniteType,
              Scheme.ModuleDerived.mPseudoCoherentOverAffine
                (𝒰.f i ≫ 𝒱.openCover.pullbackHom f j) h_finiteType m
                (((RingedSpace.Hom.IsFlat.exactPullback
                  (𝒰.f i ≫ (𝒱.openCover.pullback₁ f).f j).toShHom).mapDerivedCategory).obj E))

/- Definition 37.59.2 (2): an object of `D(𝒪_X)` is relatively pseudo-coherent
exactly when it is relatively `m`-pseudo-coherent for every `m : ℤ`. -/
@[stacks 09UI] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.pseudoCoherentOver_iff_forall_mPseudoCoherentOver :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (E : RingedSpace.ModuleDerived X.toRingedSpace),
      Scheme.ModuleDerived.IsPseudoCoherentOver f E ↔
        ∀ m : ℤ, Scheme.ModuleDerived.IsMPseudoCoherentOver f E m)

/- Definition 37.59.2 (3): a module is relatively `m`-pseudo-coherent exactly when
its degree-zero derived realization is relatively `m`-pseudo-coherent. -/
@[stacks 09UI] #check
  (AlgebraicGeometry.Scheme.Modules.isMPseudoCoherentOver_iff_single :
    ∀ {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [LocallyOfFiniteType f] (m : ℤ),
      F.IsMPseudoCoherentOver f m ↔
        Scheme.ModuleDerived.IsMPseudoCoherentOver f
          ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F) m)

/- Definition 37.59.2 (4): a module is relatively pseudo-coherent exactly when
its degree-zero derived realization is relatively pseudo-coherent. -/
@[stacks 09UI] #check
  (AlgebraicGeometry.Scheme.Modules.isPseudoCoherentOver_iff_single :
    ∀ {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [LocallyOfFiniteType f],
      F.IsPseudoCoherentOver f ↔
        Scheme.ModuleDerived.IsPseudoCoherentOver f
          ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F))

/- Relative pseudo-coherence of a scheme module is equivalent to relative
`m`-pseudo-coherence in every degree. -/
#check (AlgebraicGeometry.Scheme.Modules.isPseudoCoherentOver_iff_forall_m :
  ∀ {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S) [LocallyOfFiniteType f],
    F.IsPseudoCoherentOver f ↔ ∀ m : ℤ, F.IsMPseudoCoherentOver f m)
