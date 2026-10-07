module

public import stacks_project.Chap52.Lemma_52_25_1
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.ComparisonEulerCharacteristic
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

/- 52.25.1.1: An admissible coherent comparison computes the Euler value as the
closed-fiber cokernel length minus the closed-fiber kernel length over `A`. -/
@[stacks 0F24] #check (AlgebraicGeometry.Scheme.Modules.comparisonEulerCharacteristic_eq :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A) (hf_regular : IsRegular f),
    let S := AffineAlgebraizationSetup.ofIdeals (Ideal.span {f})
      (IsLocalRing.maximalIdeal A)
      ((Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hf_mem)
    let U₀ := S.y ⁻¹ᵁ S.U
    let sX := (Scheme.ΓSpecIso (CommRingCat.of A)).inv f
    let sU := S.U.ι.appTop sX
    ∀ (F : S.U.toScheme.Modules) (F₀ : S.Y.Modules) [F.IsCoherent] [F₀.IsCoherent],
      (∀ V : S.U.toScheme.Opens, Function.Injective
        (F.smul (S.U.toScheme.presheaf.map V.leTop.op sU)).hom) →
      ∀ (α : (Scheme.Modules.pullback (S.y ∣_ S.U)).obj F ≅ F₀.restrict U₀.ι)
        (F' : S.X.Modules) [F'.IsCoherent],
        (∀ V : S.X.Opens,
          Function.Injective (F'.smul (S.X.presheaf.map V.leTop.op sX)).hom) →
        ∀ (α' : F'.restrict S.U.ι ≅ F)
          (α₀' : (Scheme.Modules.pullback S.y).obj F' ⟶ F₀),
          (Scheme.Modules.pullback (S.y ∣_ S.U)).map α'.hom ≫ α.hom =
            (Scheme.Modules.pullbackRestrictIso S.y S.U F').hom ≫
              (Scheme.Modules.restrictFunctor U₀.ι).map α₀' →
          let linearMap := (S.y.globalSectionsFunctor.map α₀').hom
          Scheme.Modules.sectionLengthDefect S.y α₀' =
            ((Module.length A (S.y.globalSectionsMod F₀ ⧸ linearMap.range)).toNat : ℤ) -
              ((Module.length A linearMap.ker).toNat : ℤ))
