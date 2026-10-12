/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Coherator.Exact
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Coherator.Comparison

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a qcqs scheme covered by two compact opens, the canonical ambient Mayer–Vietoris
triangle becomes, after applying the coherator, a triangle isomorphic to a distinguished triangle
whose vertices are the global coherator and the two open coherator pushforwards. -/
theorem mayerVietorisDistinguished (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (U V : CompactOpens X) (hUV : U ⊔ V = ⊤)
    (K : RingedSpace.ModuleDerived X.toRingedSpace) :
    ∃ δ : RingedSpace.OpenSubspace.Pushforward.alongDerived
        (𝟙 X.toRingedSpace) (U ⊓ V).toOpens ⟶
        RingedSpace.moduleDerivedPushforward (𝟙 X.toRingedSpace) ⋙
          shiftFunctor (RingedSpace.ModuleDerived X.toRingedSpace) (1 : ℤ),
      ∃ (f : (Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint.obj K ⟶
          (openPushforwardCoherator X U).obj K ⊞ (openPushforwardCoherator X V).obj K)
        (g : (openPushforwardCoherator X U).obj K ⊞ (openPushforwardCoherator X V).obj K ⟶
          (openPushforwardCoherator X (U ⊓ V)).obj K)
        (h : (openPushforwardCoherator X (U ⊓ V)).obj K ⟶
          ((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint.obj K)⟦(1 : ℤ)⟧),
        IsIsomorphic
            (((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint.mapTriangle).obj
              (Triangle.mk
                ((biprod.lift
                  (RingedSpace.OpenSubspace.Pushforward.derivedUnit
                    (𝟙 X.toRingedSpace) U.toOpens)
                  (RingedSpace.OpenSubspace.Pushforward.derivedUnit
                    (𝟙 X.toRingedSpace) V.toOpens)).app K)
                ((biprod.desc
                  (RingedSpace.OpenSubspace.Pushforward.derivedRestriction
                    (𝟙 X.toRingedSpace)
                    Set.inter_subset_left)
                  (-(RingedSpace.OpenSubspace.Pushforward.derivedRestriction
                    (𝟙 X.toRingedSpace)
                    Set.inter_subset_right))).app K)
                (δ.app K)))
            (Triangle.mk f g h) ∧
          Triangle.mk f g h ∈ distTriang (Scheme.ModuleDerived.Quasicoherent X) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
