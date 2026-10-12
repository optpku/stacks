/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections

@[expose] public section

open CategoryTheory RingedSpace.Hom.IsFlat
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver

/-- A quasi-coherent derived object is relatively `m`-pseudo-coherent exactly when its
derived sections are relatively `m`-pseudo-coherent on the members of affine covers of the
inverse images of one affine cover of the base. -/
theorem iff_affineCoverSections {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (E : Scheme.DerivedQCoh X) (m : ℤ) :
    IsMPseudoCoherentOver f E.obj m ↔
      ∃ 𝒱 : S.AffineOpenCover.{u}, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover.{u}, ∀ i : 𝒰.I₀,
          ∃ h_finiteType :
              (Scheme.Hom.appTop (𝒰.f i ≫ 𝒱.openCover.pullbackHom f j)).hom.FiniteType,
            @DerivedCategory.IsMPseudoCoherentRelativeTo
              (Scheme.globalSectionsRing (Spec (𝒱.X j))) _
              (Scheme.globalSectionsRing (Spec (𝒰.X i))) _
              (Scheme.Hom.appTop (𝒰.f i ≫ 𝒱.openCover.pullbackHom f j)).hom.toAlgebra
              h_finiteType
              ((RingedSpace.moduleDerivedGlobalSections (Spec (𝒰.X i)).toRingedSpace).obj
                (((exactPullback
                  (𝒰.f i ≫ (𝒱.openCover.pullback₁ f).f j).toShHom).mapDerivedCategory).obj
                    E.obj)) m := sorry

/-- Relative `m`-pseudo-coherence of a quasi-coherent derived object is equivalent to
relative `m`-pseudo-coherence of its derived sections on every compatible pair of affine
opens. -/
theorem iff_affineSections {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (E : Scheme.DerivedQCoh X) (m : ℤ) :
    IsMPseudoCoherentOver f E.obj m ↔
      ∀ (V : S.affineOpens) (U : X.affineOpens)
        (e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)),
        @DerivedCategory.IsMPseudoCoherentRelativeTo
          Γ(S, (V : S.Opens)) _ Γ(X, (U : X.Opens)) _
          (Scheme.Hom.sectionsAlgebra f V U e)
          (f.finiteType_appLE V.property U.property e)
          ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace U).obj E.obj) m := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver
