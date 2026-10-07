module

public import ReasLib.AlgebraicGeometry.Scheme.Module.DescentLocus.Cohomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 37.33.5: let `X' ⟶ X` be a morphism over `S`, with both structure maps flat,
proper, and finitely presented and satisfying the base-change structure-sheaf condition from
`Lemma 37.33.1`. For an invertible module `L` on `X`, suppose `j : Z ⟶ S` and
`j' : Z' ⟶ S` represent the descent loci of `L` and its pullback, and `i : Z ⟶ Z'` is their
inclusion over `S`. If `s` lies in `Z` and the canonical map
`H¹(X_s, 𝒪) ⟶ H¹(X'_s, 𝒪)` is injective, then `i` is an isomorphism over an open
neighborhood of `s`. -/
@[stacks 0BF1] #check
  (AlgebraicGeometry.Scheme.Modules.descentLoci_eq_near_of_fiberH1_injective :
    ∀ {X' X S Z Z' : Scheme.{u}} (p : X' ⟶ X) (f' : X' ⟶ S) (f : X ⟶ S)
    (sq : CommSq p f' f (𝟙 S))
    [Flat f'] [IsProper f'] [Scheme.Hom.FinitePresentation f']
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    (h_unit' : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso (SheafOfModules.unitToPushforwardObjUnit
        (pullback.snd f' g).toRingCatSheafHom))
    (h_unit : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      IsIso (SheafOfModules.unitToPushforwardObjUnit
        (pullback.snd f g).toRingCatSheafHom))
    (L : X.Modules) [Invertible L]
    (j : Z ⟶ S) [IsImmersion j] [Scheme.Hom.FinitePresentation j]
    (j' : Z' ⟶ S) [IsImmersion j'] [Scheme.Hom.FinitePresentation j']
    (hZ : RepresentsDescentLocus f L j)
    (hZ' : RepresentsDescentLocus f' ((Scheme.Modules.pullback p).obj L) j')
    (i : Z ⟶ Z') (h_i : i ≫ j' = j) (s : S) (h_s : s ∈ Set.range j.base)
    (hH1 : Function.Injective
      ((Scheme.Hom.fiberMap f' p (𝟙 S) f sq s).structureSheafCohomologyMap 1)),
    ∃ U : S.Opens, s ∈ U ∧ IsIso (i ∣_ (j' ⁻¹ᵁ U)))

end AlgebraicGeometry.Scheme.Modules
