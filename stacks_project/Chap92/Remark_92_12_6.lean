/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.Tensor.MultiplicationKernel
public import ReasLib.Algebra.Category.ModuleCat.Tor.Surjective
public import ReasLib.RingTheory.Extension.Presentation.LengthTwo.Tor
public import ReasLib.RingTheory.CotangentComplex.DegreeTwo
import StacksCheckRecall

/-!
# Degree-two identifications of the cotangent complex

The mixed tensor in Remark 92.12.6 factors through `J₀/J₀²`: tensor balancing
annihilates the representatives in `J₀²`. The displayed middle summand is
therefore interpreted as the conormal module with its natural `B`-scalars.

The faces of Example 92.5.9 satisfy `d₀(xₜ) = 0` and `d₁(xₜ) = fₜ`.
With the ordered wedge tensor `xₜ ⊗ xₜ′ - xₜ′ ⊗ xₜ`, their difference
`d₀ - d₁` gives `fₜ′ ⊗ fₜ - fₜ ⊗ fₜ′`. This is the negative of the exterior
face formula printed in the remark. The mixed face formula and the final
right-exact sequence agree with these face conventions.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialObject
open Algebra Algebra.CotangentComplex Algebra.PolynomialSite
open Algebra.Presentation.LengthTwo Ideal
open scoped Simplicial TensorProduct

universe u

variable {A B ι σ : Type u} [CommRing A] [CommRing B] [Algebra A B]

/- Remark 92.12.6. The explicit tensor face cokernel computes the actual
degree-minus-two homology of the cotangent complex. The comparisons, concrete
summand maps, and right-exact sequence are checked below. -/
@[stacks 09D6] #check
  (Algebra.Presentation.LengthTwo.cokerFaceSub_isIsomorphic_cotangentHomology_negTwo :
    ∀ P : Presentation A B ι σ,
      IsIsomorphic (cokerFaceSub P) ((Algebra.cotangentComplex A B).homology (-2)))

section PolynomialArrow

variable (X : Algebra.PolynomialOver A B)
variable (h : Function.Surjective X.obj.hom.hom.toRingHom)

#check (ModuleCat.ExtendScalars.selfTorTwo_isIsomorphic_kernelTorOne
    X.obj.hom.hom.toRingHom h :
  IsIsomorphic (ModuleCat.ExtendScalars.selfTorObj X.obj.hom.hom.toRingHom 2)
    (CommAlgCat.Over.Polynomial.Site.kernelTorObj 1 X))

#check (ModuleCat.ExtendScalars.kernelTorOne_isIsomorphic_mulKer
    X.obj.hom.hom.toRingHom h :
  IsIsomorphic (CommAlgCat.Over.Polynomial.Site.kernelTorObj 1 X)
    (Ideal.mulKerModuleCat X.obj.hom.hom.toRingHom h))

end PolynomialArrow

section Resolution

variable {P : SimplicialObject (CommAlgCat.{u} A)}
variable (ε : P ⟶ (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B)) [IsResolution ε]

#check (Algebra.CotangentComplex.cotangentHomology_negTwo_isIsomorphic_coker_faceSub ε :
  IsIsomorphic ((Algebra.cotangentComplex A B).homology (-2))
    (cokernel (kernelTorFaceSub ε)))

end Resolution

section Presentation

variable (P : Presentation A B ι σ)

#check (Algebra.Presentation.LengthTwo.torTwoTerm1SourceModuleCat P : ModuleCat.{u} B)

#check (Algebra.Presentation.LengthTwo.wedgeIncl P :
  ⋀[B]^2 (σ →₀ B) →ₗ[B] term1MulKerModuleCat P)

#check (Algebra.Presentation.LengthTwo.mixedIncl P :
  (σ →₀ kerCotangentModuleCat P) →+ term1MulKerModuleCat P)

#check (Algebra.Presentation.LengthTwo.degeneracyIncl P :
  term0MulKerModuleCat P →+ term1MulKerModuleCat P)

#check (Algebra.Presentation.LengthTwo.torTwoTerm1CoprodLM P :
  torTwoTerm1SourceModuleCat P →ₗ[B] term1MulKerModuleCat P)

#check (Algebra.Presentation.LengthTwo.torTwoTerm1Coprod_bijective P :
  Function.Bijective (torTwoTerm1CoprodLM P))

#check (Algebra.Presentation.LengthTwo.wedgeIncl_apply P : ∀ t t' : σ,
  wedgeIncl P (exteriorPower.ιMulti B 2 fun i =>
    Finsupp.single (if i = 0 then t else t') (1 : B)) =
    alternTmul (xKer P t) (xKer P t'))

#check (Algebra.Presentation.LengthTwo.mixedIncl_apply P : ∀ (t : σ) (f : P.ker),
  mixedIncl P (Finsupp.single t (P.ker.toCotangent f)) =
    alternTmul (xKer P t) (degeneracyZero_mapKer P f))

#check (Algebra.Presentation.LengthTwo.mixedIncl_apply_eq_zero_of_mem_sq P :
  ∀ (t : σ) (f : P.ker), (f : P.Ring) ∈ P.ker ^ 2 →
    mixedIncl P (Finsupp.single t (P.ker.toCotangent f)) = 0)

#check (Algebra.Presentation.LengthTwo.faceSub_degeneracyIncl P :
  (faceSub P).comp (degeneracyIncl P) = 0)

#check (Algebra.Presentation.LengthTwo.faceSub_mixedIncl P : ∀ (t : σ) (f : P.ker),
  faceSub P (mixedIncl P (Finsupp.single t (P.ker.toCotangent f))) =
    alternTmul f (relationKer P t))

#check (Algebra.Presentation.LengthTwo.faceSub_wedgeIncl P : ∀ t t' : σ,
  faceSub P (wedgeIncl P (exteriorPower.ιMulti B 2 fun i =>
    Finsupp.single (if i = 0 then t else t') (1 : B))) =
    alternTmul (relationKer P t') (relationKer P t))

#check (Algebra.Presentation.LengthTwo.faceSubLM P :
  term1MulKerModuleCat P →ₗ[B] term0MulKerModuleCat P)

#check (Ideal.conormalExteriorSquareToMulKer P.ker :
  ⋀[P.Ring ⧸ P.ker]^2 P.ker.Cotangent →ₗ[P.Ring ⧸ P.ker]
    mulKerQuotientModuleCat P.ker)

#check (Ideal.conormalExteriorSquareToMulKer_apply P.ker : ∀ a b : P.ker,
  conormalExteriorSquareToMulKer P.ker
      (exteriorPower.ιMulti (P.Ring ⧸ P.ker) 2 fun i =>
        if i = 0 then P.ker.toCotangent a else P.ker.toCotangent b) =
    alternTmul a b)

#check (Algebra.Presentation.LengthTwo.cokerFaceSubMkQ P :
  term0MulKerModuleCat P →ₗ[B] cokerFaceSub P)

#check (Algebra.Presentation.LengthTwo.exact_conormalExteriorSquare_cokerFaceSub P :
  Function.Exact (conormalExteriorSquareToMulKer P.ker) (cokerFaceSubMkQ P))

#check (Algebra.Presentation.LengthTwo.cokerFaceSubMkQ_surjective P :
  Function.Surjective (cokerFaceSubMkQ P))

end Presentation


