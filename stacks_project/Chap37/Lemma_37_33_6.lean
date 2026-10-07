module

public import ReasLib.AlgebraicGeometry.Scheme.Module.DescentLocus.Cohomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 37.33.6: for a finite family of morphisms `Xᵢ i ⟶ X` over `S`, let `Z`
and `Zᵢ i` represent the descent loci of an invertible module `L` and its pullbacks.
If `Z` maps into every `Zᵢ i` over `S`, `s` lies in `Z`, and the combined map
`H¹(X_s, 𝒪) ⟶ ∀ i, H¹(Xᵢ_s, 𝒪)` is injective, then near `s`, factoring through `Z`
is equivalent to factoring through every `Zᵢ i`. -/
@[stacks 0BF2] #check
  (AlgebraicGeometry.Scheme.Modules.descentLocus_eq_iInter_near_of_fiberH1_injective :
    ∀ (n : ℕ) {X S Z : Scheme.{u}} (Xᵢ Zᵢ : Fin n → Scheme.{u})
      (p : ∀ i, Xᵢ i ⟶ X) (fᵢ : ∀ i, Xᵢ i ⟶ S) (f : X ⟶ S)
      (sq : ∀ i, CommSq (p i) (fᵢ i) f (𝟙 S))
      [∀ i, Flat (fᵢ i)] [∀ i, IsProper (fᵢ i)]
      [∀ i, Scheme.Hom.FinitePresentation (fᵢ i)]
      [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
      (h_unitᵢ : ∀ i {T : Scheme.{u}} (g : T ⟶ S),
        IsIso (SheafOfModules.unitToPushforwardObjUnit
          (pullback.snd (fᵢ i) g).toRingCatSheafHom))
      (h_unit : ∀ {T : Scheme.{u}} (g : T ⟶ S),
        IsIso (SheafOfModules.unitToPushforwardObjUnit
          (pullback.snd f g).toRingCatSheafHom))
      (L : X.Modules) [Invertible L]
      (j : Z ⟶ S) [IsImmersion j] [Scheme.Hom.FinitePresentation j]
      (jᵢ : ∀ i, Zᵢ i ⟶ S) [∀ i, IsImmersion (jᵢ i)]
      [∀ i, Scheme.Hom.FinitePresentation (jᵢ i)]
      (hZ : RepresentsDescentLocus f L j)
      (hZᵢ : ∀ i, RepresentsDescentLocus (fᵢ i)
        ((Scheme.Modules.pullback (p i)).obj L) (jᵢ i))
      (inc : ∀ i, Z ⟶ Zᵢ i) (h_inc : ∀ i, inc i ≫ jᵢ i = j)
      (s : S) (h_s : s ∈ Set.range j.base)
      (hH1 : Function.Injective (fun x ↦ fun i ↦
        ((Scheme.Hom.fiberMap (fᵢ i) (p i) (𝟙 S) f (sq i) s).structureSheafCohomologyMap
          1) x)),
      ∃ U : S.Opens, s ∈ U ∧ ∀ {T : Scheme.{u}} (g : T ⟶ U.toScheme),
        Nonempty (Over.mk g ⟶ Over.mk (j ∣_ U)) ↔
          ∀ i, Nonempty (Over.mk g ⟶ Over.mk (jᵢ i ∣_ U)))

end AlgebraicGeometry.Scheme.Modules
