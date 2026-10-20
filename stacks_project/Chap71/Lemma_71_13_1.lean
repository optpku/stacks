/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap71.Lemma_71_11_4_Psi
public import stacks_project.Chap71.Lemma_71_13_1_BaseChange
public import stacks_project.Chap71.Lemma_71_13_1_Canonical
public import stacks_project.Chap71.Lemma_71_13_1_SectionMap

/-!
# Lemma 71.13.1

A graded map from a pulled-back quasi-coherent algebra into the tensor powers of an
invertible module on an algebraic space induces a canonical open `U(ψ)`, a morphism
`r_{L,ψ}` into relative Proj over the base, and a graded twist comparison `θ`,
characterized by étale section squares, classification of scheme tests, and base
change to schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.RelativeProj
open Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : X ⟶ Y)
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y)}
variable (deg : DegreePieces 𝒜) {F : ProjFunctor Y 𝒜}
variable (hF : F.IsAssociatedToQuadruples deg) (L : X.Modules)
variable [isInvertibleObject L] (ψ : GradedMapToPowers f deg L)

/-- Lemma 71.13.1 (1)
For `V` étale over `Y` and `d ≥ 0`, the two paths
`𝒜_d(V) → Γ(V ×_Y X, L^{⊗ d}) → Γ(V ×_Y U(ψ), L^{⊗ d})`
and
`𝒜_d(V) → Γ(V ×_Y underline{Proj}_Y(𝒜), 𝒪(d)) → Γ(V ×_Y U(ψ), L^{⊗ d})`
agree, after identifying the first path with the adjoint of `ψ` restricted to `U(ψ)`
and the second path with the pushforward of `θ` along `π`. -/
@[stacks 0D2Z]
theorem theta_commutes (d : ℕ) :
    psiPushforward f deg L ψ d ≫ restrictPushforward f deg L ψ d =
      ((Modules.pullbackPushforwardAdjunction
            (toAlgebraicSpace_hom F hF)).homEquiv
          (deg.obj d) (CanonicalTwists.obj F hF (Int.ofNat d)))
        ((CanonicalTwists.psi F hF).hom d) ≫
        thetaPushforwardToBase f deg hF L ψ d :=
  sorry

/-- Lemma 71.13.1 (2)
If `W` is a scheme over `X` and `d ≥ 1` is such that
`ψ|_W : f^* 𝒜_d|_W ⟶ L^{⊗ d}|_W` is an epimorphism, then `W ⟶ X` factors through
`U(ψ)`. -/
@[stacks 0D2Z]
theorem factorsThrough_of_epi {W : Over S} (w : ofOver W ⟶ X) (d : ℕ)
    (hd : 1 ≤ d) (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    factorsThroughLift f deg L ψ w (memDomain_of_epi f deg L ψ w d hd hEpi) ≫
        (SectionMap.canonical f deg hF L ψ).domain.ι =
      w :=
  sorry

/-- Lemma 71.13.1 (3)
If `W` is a quasi-compact scheme over `X` and `d ≥ 1` is such that
`ψ|_W : f^* 𝒜_d|_W ⟶ L^{⊗ d}|_W` is an epimorphism, then the composite of the
factorization through `U(ψ)` with `r_{L,ψ}` is the morphism
`W ⟶ underline{Proj}_Y(𝒜)` classified by the restricted quadruple of
Definition 71.11.3. -/
@[stacks 0D2Z]
theorem classifiedMap_comp {W : Over S} [CompactSpace W.left]
    (w : ofOver W ⟶ X) (d : ℕ) (hd : 1 ≤ d)
    (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    factorsThroughLift f deg L ψ w (memDomain_of_epi f deg L ψ w d hd hEpi) ≫
        (SectionMap.canonical f deg hF L ψ).map =
      yonedaEquiv.symm
        (hF.pointOf W (restrictedQuadruple f deg L ψ w d hd hEpi)) :=
  sorry

/-- For a general scheme test, the composite with `r_{L,ψ}` is the glueing of the
Definition 71.11.3 classifying maps on quasi-compact opens, using the same degree. -/
theorem classifiedMap_comp_of {W : Over S} (w : ofOver W ⟶ X) (d : ℕ)
    (hd : 1 ≤ d) (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)) :
    factorsThroughLift f deg L ψ w (memDomain_of_epi f deg L ψ w d hd hEpi) ≫
        (SectionMap.canonical f deg hF L ψ).map =
      classifiedMapOfDegree f deg hF L ψ w d hd hEpi :=
  sorry

section SchemeBaseChange

variable {Y' X' : Over S}
variable {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift (ofOver Y'))}
variable {deg' : DegreePieces 𝒜'} {F' : ProjFunctor (ofOver Y') 𝒜'}
variable (g : ofOver Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
variable (hF' : F'.IsAssociatedToQuadruples deg')
variable (g' : ofOver X' ⟶ X) (f' : ofOver X' ⟶ ofOver Y')
variable (hf : g' ≫ f = f' ≫ g)
variable [isInvertibleObject ((Modules.pullback g').obj L)]

/-- Lemma 71.13.1 (4)
For a commutative square of algebraic spaces with scheme vertices `X'` and `Y'`,
writing `𝒜' = g^* 𝒜`, `L' = (g')^* L`, and `ψ'` for the pullback of `ψ`, the
canonical open `U(ψ')` is identified with `(g')^{-1}(U(ψ))` over `X'`. The scheme
case of this identification is the construction recorded in tag 01O9. -/
@[stacks 0D2Z]
theorem baseChange_domain :
    (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom ≫
        (domainInverseImage f deg L ψ g').ι =
      (SectionMap.canonical f' deg' hF' ((Modules.pullback g').obj L)
            (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).domain.ι :=
  sorry

/-- Lemma 71.13.1 (5)
In the square of Lemma 71.13.1 (4), the canonical morphism `r_{L',ψ'}` equals
the base change of `r_{L,ψ}` along `domainBaseChangeIso`, compared with relative
Proj of `𝒜'` via `canonicalBaseChangeIso` of Lemma 71.11.5. The scheme case is
the uniqueness recorded in tag 01O9. -/
@[stacks 0D2Z]
theorem baseChange_map :
    (SectionMap.canonical f' deg' hF' ((Modules.pullback g').obj L)
          (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).map =
      (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom ≫
        baseChangeMap f deg L ψ hF g hAlg hF' g' f' :=
  sorry

/-- After composing with `canonicalBaseChangeIso`, the canonical morphism of the
pulled-back data is the fibre-product lift of `r_{L,ψ}`. -/
theorem baseChange_map_fibre :
    (SectionMap.canonical f' deg' hF' ((Modules.pullback g').obj L)
          (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).map ≫
        (canonicalBaseChangeIso g hAlg hF hF').hom =
      (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom ≫
        baseChangeToFibre f deg L ψ hF g g' f' :=
  sorry

/-- Lemma 71.13.1 (6)
In the square of Lemma 71.13.1 (4), after the identifications of Lemma 71.13.1 (4)
and Lemma 71.13.1 (5), the canonical twist comparison `θ'` is the transport of the
pullback of `θ` along `CanonicalTwists.BaseChange.degreeIso`. The scheme case is
the uniqueness recorded in tag 01O9. -/
@[stacks 0D2Z]
theorem baseChange_theta (n : ℕ) :
    (SectionMap.canonical f' deg' hF' ((Modules.pullback g').obj L)
          (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).theta n =
      thetaCanonicalBaseChange f deg L ψ hF g hAlg hF' g' f' hf n :=
  sorry

end SchemeBaseChange

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
