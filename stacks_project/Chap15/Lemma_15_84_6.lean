module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.BaseChange.Tensor.Relative
import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Model
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.84.6 (Stacks `0E1U`)

@stack 0E1U

The source has a basic model/computation layer, its tensor-product base-change clause, and a
finite-presentation refinement.  A flat map `R → A`, a pseudo-coherent source `K`, and finite Tor
dimension of `L` over `R` give one bounded-above finite-free source model, one bounded relatively
flat target model, and one bounded-below relatively flat Hom model.  When `L` is perfect over `R`
and the map is of finite presentation, the same witnesses can be chosen termwise finitely
presented.  The canonical ReasLib producers own the shared compositions; the tagged checks below
preserve the source-facing hypotheses and the common witnesses.
-/

open CategoryTheory
open CochainComplex.HomComplex
open scoped TensorProduct Algebra.TensorProduct.Right

universe u

namespace CategoryTheory.DerivedCategory.InternalHom

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable [Module.Flat R A]
variable {K L : DerivedCategory (ModuleCat A)}

/- Lemma 15.84.6, choices (1)--(2) and conclusion (a): a pseudo-coherent source and a target of
finite Tor dimension over `R` have common bounded source, target, and derived internal-Hom models.
The complete witness statement is owned by the reusable `InternalHom.Model.Relative` leaf. -/
@[stacks 0E1U "choices (1)-(2) and conclusion (a), common finite-Tor models"]
#check fun (hK : K.IsPseudoCoherent) (hL : L.HasFiniteTorDimensionOver R) =>
  (DerivedCategory.InternalHom.RHom.FiniteTorModel.nonempty hK hL :
    Nonempty (DerivedCategory.InternalHom.RHom.FiniteTorModel R K L))
#check @DerivedCategory.IsPseudoCoherent.exists_internalHom_model

end CategoryTheory.DerivedCategory.InternalHom

/- The representative producers and fixed-model consumers remain directly reusable. -/
#check @DerivedCategory.IsPseudoCoherent.exists_finiteFree_model
#check @DerivedCategory.IsPerfectOver.isPseudoCoherent
#check @DerivedCategory.IsPerfectOver.hasFiniteTorDimensionOver
#check @DerivedCategory.IsPerfectOver.exists_flat_finitePresentation_model
#check @CochainComplex.HomComplex.plus
#check @CochainComplex.HomComplex.isTermwiseFlatOver
#check @HomologicalComplex.isTermwiseFlat_restrictScalarsAlong_iff
#check @CochainComplex.HomComplex.isTermwiseFinitePresentation
#check @CochainComplex.ProjectiveMinus.representsRHom_of_models
#check @HomologicalComplex.IsTermwiseFiniteProjective.of_finiteFree

#check @CochainComplex.HomComplex.Pushout.Tensor.plus
#check @CochainComplex.HomComplex.Pushout.Tensor.isTermwiseFlatOver

/- Lemma 15.84.6 (b): for every ring map `R → R'`, with `A' = A ⊗[R] R'`, the same Hom model
after the canonical tensor-product base change (`E ⊗[R] R'`, exposed by `cochainIso`) computes the
canonical `RHom` over `A'`. -/
@[stacks 0E1U "conclusion (b), base change"]
#check fun {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [Module.Flat R A]
    {K L : DerivedCategory (ModuleCat A)}
    (M : DerivedCategory.InternalHom.RHom.FiniteTorModel R K L) =>
  (M.baseChange (R' := R') :
    IsIsomorphic
      (DerivedCategory.Q.obj
        (ModuleCat.Pushout.Tensor.algebraBaseChange
          (moduleComplex A M.source M.target)))
      (DerivedCategory.InternalHom.RHom.obj (A := A ⊗[R] R')
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap A (A ⊗[R] R'))).obj K)
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap A (A ⊗[R] R'))).obj L)))
#check @CategoryTheory.DerivedCategory.InternalHom.RHom.PerfectModel.baseChange
#check @CochainComplex.HomComplex.Pushout.Tensor.representsRHom_of_finiteFree
#check @CochainComplex.HomComplex.Pushout.Tensor.representsRHom_of_bounded

/- Lemma 15.84.6, finite-presentation refinement: if `R → A` is of finite presentation and `L` is
perfect over `R`, the common witnesses can additionally be chosen termwise finitely presented.
The source-faithful specialization is owned by the reusable `InternalHom.Model.Relative` leaf. -/
@[stacks 0E1U "finite-presentation refinement"]
#check fun {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    {K L : DerivedCategory (ModuleCat A)}
    (hK : K.IsPseudoCoherent) (hL : L.IsPerfectOver R) =>
  (DerivedCategory.InternalHom.RHom.PerfectModel.nonempty hK hL :
    Nonempty (DerivedCategory.InternalHom.RHom.PerfectModel R K L))
#check @DerivedCategory.IsPerfectOver.FinitePresentation.exists_internalHom_model
#check @DerivedCategory.IsPerfectOver.exists_internalHom_model

#check @ModuleCat.Pushout.Tensor.algebraBaseChange
#check @ModuleCat.Pushout.Tensor.cochainIso
#check @ModuleCat.derivedExtensionOfScalars

#check @DerivedCategory.IsPerfectOver.iff_exists_flat_finitePresentation_model
