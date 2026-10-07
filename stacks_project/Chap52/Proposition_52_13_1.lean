module

public import stacks_project.Chap52.Proposition_52_12_3
public import stacks_project.Chap52.Proposition_52_13_1_Comparison

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- Proposition 52.13.1 (1): for nested ideals `I ⊆ 𝔞` in a Noetherian ring `A`,
a coherent module `F` on `U = Spec(A) ∖ V(𝔞)`, and `s : ℕ`, assume `A` is
`I`-adically complete and has a dualizing complex. If every `x ∈ U ∖ V(I)` satisfies
the stated depth alternative and either `F|_{U ∖ V(I)}` satisfies `(S_{s + 1})` or
`V(𝔞)` has dimension-function spread at most two, then
`H^i(U, F) ⟶ lim_n H^i(U, F / I ^ (n + 1)F)` is an isomorphism for every `i < s`. -/
@[stacks 0EG4]
theorem cohomologyComparison_isIso_of_depth
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (S : AffineAlgebraizationSetup A)
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    [IsAdicComplete S.I A]
    (F : RingedSpace.Coh (S.U.toScheme).toRingedSpace) (s : ℕ)
    (h_depth : ∀ x : S.U,
      S.U.ι x ∉ (idealSheafDataOfIdealOnSpec S.I).support →
        (s : EInt) <
            ((WithTop.map Int.ofNat
              (moduleDepth ((S.U.toScheme).presheaf.stalk x)
                (RingedSpace.stalkModuleCat F.obj x)) : WithTop ℤ) : EInt) ∨
          ∀ z : PointClosure.scheme (S.U.ι x),
            PointClosure.ι (S.U.ι x) z ∈ S.U.compl →
              ((Ideal.LocalCohomology.dimension S.I
                  S.I.fg_of_isNoetherianRing + s + 1 : ℤ) : EInt) <
                ((WithTop.map Int.ofNat
                  (moduleDepth ((S.U.toScheme).presheaf.stalk x)
                    (RingedSpace.stalkModuleCat F.obj x)) : WithTop ℤ) : EInt) +
                  WithBot.map (WithTop.map Int.ofNat)
                    (ringKrullDim
                      ((PointClosure.scheme (S.U.ι x)).presheaf.stalk z)))
    (h_alternative :
      @satisfiesSerreConditionS
          (idealOnOpen S).openComplement.toScheme inferInstance
          ((coherentRestrictFunctor
            (idealOnOpen S).openComplement.ι).obj F).obj
          ((coherentRestrictFunctor
            (idealOnOpen S).openComplement.ι).obj F).property (s + 1) ∨
        ∃ δ : S.X → ℤ, IsDimensionFunction δ ∧
          ∃ δmax δmin : ℤ,
            IsGreatest (δ '' S.U.compl) δmax ∧
              IsLeast (δ '' S.U.compl) δmin ∧ δmax - δmin ≤ 2) :
    ∀ i : ℕ, i < s → IsIso (cohomologyComparison S F.obj i) := sorry

/-- Proposition 52.13.1 (2): under the same completeness, dualizing-complex, depth,
and `(S_{s + 1})` or dimension-function hypotheses, the canonical map
`colim_{V ⊇ U ∩ V(I)} H^s(V, F) ⟶ lim_n H^s(U, F / I ^ (n + 1)F)` is an
isomorphism after forgetting the `A`-module structure on the target. -/
@[stacks 0EG4]
theorem neighborhoodCohomologyComparison_isIso_of_depth
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (S : AffineAlgebraizationSetup A)
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    [IsAdicComplete S.I A]
    (F : RingedSpace.Coh (S.U.toScheme).toRingedSpace) (s : ℕ)
    (h_depth : ∀ x : S.U,
      S.U.ι x ∉ (idealSheafDataOfIdealOnSpec S.I).support →
        (s : EInt) <
            ((WithTop.map Int.ofNat
              (moduleDepth ((S.U.toScheme).presheaf.stalk x)
                (RingedSpace.stalkModuleCat F.obj x)) : WithTop ℤ) : EInt) ∨
          ∀ z : PointClosure.scheme (S.U.ι x),
            PointClosure.ι (S.U.ι x) z ∈ S.U.compl →
              ((Ideal.LocalCohomology.dimension S.I
                  S.I.fg_of_isNoetherianRing + s + 1 : ℤ) : EInt) <
                ((WithTop.map Int.ofNat
                  (moduleDepth ((S.U.toScheme).presheaf.stalk x)
                    (RingedSpace.stalkModuleCat F.obj x)) : WithTop ℤ) : EInt) +
                  WithBot.map (WithTop.map Int.ofNat)
                    (ringKrullDim
                      ((PointClosure.scheme (S.U.ι x)).presheaf.stalk z)))
    (h_alternative :
      @satisfiesSerreConditionS
          (idealOnOpen S).openComplement.toScheme inferInstance
          ((coherentRestrictFunctor
            (idealOnOpen S).openComplement.ι).obj F).obj
          ((coherentRestrictFunctor
            (idealOnOpen S).openComplement.ι).obj F).property (s + 1) ∨
        ∃ δ : S.X → ℤ, IsDimensionFunction δ ∧
          ∃ δmax δmin : ℤ,
            IsGreatest (δ '' S.U.compl) δmax ∧
              IsLeast (δ '' S.U.compl) δmin ∧ δmax - δmin ≤ 2) :
    IsIso (neighborhoodCohomologyComparison S F.obj s) := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
