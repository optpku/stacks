/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.Topology.Sheaves.Abelian.Over
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module on the punctured spectrum of a Noetherian local ring, with
injective multiplication by a regular element of the maximal ideal and a coherent
closed-fiber identification, admits a coherent extension with injective multiplication
and a closed-fiber map compatible with the canonical pullback–restriction isomorphism. -/
theorem existsTorsionFreeExtension (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f) :
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    let sX := (Scheme.ΓSpecIso (CommRingCat.of A)).inv f
    let sU := S.U.ι.appTop sX
    ∀ (F : S.U.toScheme.Modules) (F₀ : S.Y.Modules) [F.IsCoherent] [F₀.IsCoherent],
      (∀ V : S.U.toScheme.Opens, Function.Injective
        (F.smul (S.U.toScheme.presheaf.map V.leTop.op sU)).hom) →
      ∀ (α : (pullback (S.y ∣_ S.U)).obj F ≅ F₀.restrict U₀.ι),
        ∃ (F' : S.X.Modules), F'.IsCoherent ∧
          (∀ V : S.X.Opens,
            Function.Injective (F'.smul (S.X.presheaf.map V.leTop.op sX)).hom) ∧
          ∃ (α' : F'.restrict S.U.ι ≅ F)
            (α₀' : (pullback S.y).obj F' ⟶ F₀),
            (pullback (S.y ∣_ S.U)).map α'.hom ≫ α.hom =
              (pullbackRestrictIso S.y S.U F').hom ≫
                (restrictFunctor U₀.ι).map α₀' := sorry

end AlgebraicGeometry.Scheme.Modules
