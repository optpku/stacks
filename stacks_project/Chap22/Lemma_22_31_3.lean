module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Derived.Bifunctor
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}
variable {T T' : DifferentialGradedBimodule A B}
variable (f : T ⟶ T') (hf : DifferentialGradedBimodule.quasiIso A B f)
variable (e : T ≅ T')

/- The underived source action is concrete precomposition, first on DG modules and then on the
homotopy category. -/
#check DifferentialGradedBimodule.InternalHom.precomp f
#check DifferentialGradedBimodule.InternalHom.precompK f

/- Lemma 22.31.3 (1) (0BYV): a bimodule morphism acts contravariantly on the actual total
right-derived internal-Hom functors. -/
@[stacks 0BYV]
#check
  (DifferentialGradedBimodule.InternalHom.derivedNatTrans f :
    DifferentialGradedBimodule.InternalHom.derivedFunctor T' ⟶
      DifferentialGradedBimodule.InternalHom.derivedFunctor T)

/- Lemma 22.31.3 (2) (0BYV): if the bimodule morphism is a quasi-isomorphism, the induced
derived natural transformation is an isomorphism. -/
#check DifferentialGradedBimodule.InternalHom.derivedNatTrans_isIso_of_quasiIso f hf

/- A strict bimodule isomorphism gives an explicit companion natural isomorphism. -/
#check DifferentialGradedBimodule.InternalHom.derivedNatIso e

/- The forward map of the derived isomorphism is the derived precomposition transformation. -/
#check DifferentialGradedBimodule.InternalHom.derivedSourceIso_inv e
#check DifferentialGradedBimodule.InternalHom.derivedNatIso_hom e
#check DifferentialGradedBimodule.InternalHom.derivedNatIso_inv e

/- The enrichment laws are owned once by total right derivation; the internal-Hom statements
below are its contravariant parameter specialization. -/
#check @CategoryTheory.Functor.RightDerived.mapNatTrans.zero
#check @CategoryTheory.Functor.RightDerived.mapNatTrans.add
#check @CategoryTheory.Functor.RightDerived.mapNatTrans.smul

/- Before localization, the parameter dependence is an additive and linear functor on the
opposite category of strict bimodules. -/
#check @DifferentialGradedBimodule.InternalHom.derivedSourceMap_zero
#check @DifferentialGradedBimodule.InternalHom.derivedSourceMap_add
#check @DifferentialGradedBimodule.InternalHom.derivedSourceMap_smul
#check @DifferentialGradedBimodule.InternalHom.derivedNatTrans_zero
#check @DifferentialGradedBimodule.InternalHom.derivedNatTrans_add
#check @DifferentialGradedBimodule.InternalHom.derivedNatTrans_smul
#check @DifferentialGradedBimodule.InternalHom.derivedBimoduleFunctor
#check @DifferentialGradedBimodule.InternalHom.derivedBimoduleFunctor_obj
#check @DifferentialGradedBimodule.InternalHom.derivedBimoduleFunctor_map
#check @DifferentialGradedBimodule.InternalHom.derivedBimoduleFunctor_inverts

#synth (DifferentialGradedBimodule.InternalHom.derivedBimoduleFunctor A B).Additive
#synth CategoryTheory.Functor.Linear R
  (DifferentialGradedBimodule.InternalHom.derivedBimoduleFunctor A B)

/- The reusable owner descends this family once to the opposite full derived category of
bimodules. -/
#check @DifferentialGradedBimodule.InternalHom.derivedBifunctor
#check @DifferentialGradedBimodule.InternalHom.derivedBifunctorFactors
#check DifferentialGradedBimodule.InternalHom.derivedBifunctorObjIso T
#check DifferentialGradedBimodule.InternalHom.derivedBifunctorObjIso.hom_naturality f
#check DifferentialGradedBimodule.InternalHom.derivedBifunctorObjIso.inv_naturality f
#check DifferentialGradedBimodule.InternalHom.derivedBifunctor_map_fromBimodules f

#synth (DifferentialGradedBimodule.InternalHom.derivedBifunctor A B).Additive
#synth CategoryTheory.Functor.Linear R
  (DifferentialGradedBimodule.InternalHom.derivedBifunctor A B)
