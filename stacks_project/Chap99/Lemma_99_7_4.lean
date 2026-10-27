/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Sheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

/- Lemma 99.7.4 (1): in Situation 99.7.1 the functor `Q_{F/X/B}` on `(Sch/B)ᵒᵖ`
satisfies the sheaf property for the fpqc topology. -/
@[stacks 082P] #check (AlgebraicGeometry.AlgebraicSpace.Quot.functor_isSheaf_fpqc :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent],
      Presheaf.IsSheaf (SchemeOver.fpqcTopology B)
        (AlgebraicGeometry.AlgebraicSpace.Quot.functor f F))

/- Compatible families of kernel-identified quotients of `F_{T_i}` on an fpqc
covering of schemes over `B` glue uniquely to a kernel-identified quotient of
`F_T`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Quot.functor_isSheafFor_fpqcCovering :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
      {ι : Type u} {U : SchemeOver B} {V : ι → SchemeOver B} (h : ∀ i, V i ⟶ U),
      Presieve.ofArrows V h ∈ SchemeOver.fpqcPrecoverage B U →
      Presieve.IsSheafFor (AlgebraicGeometry.AlgebraicSpace.Quot.functor f F)
        (Presieve.ofArrows V h))

/- Lemma 99.7.4 (2): in Situation 99.7.1 the functor `Q^{fp}_{F/X/B}` on
`(Sch/B)ᵒᵖ` satisfies the sheaf property for the fpqc topology. -/
@[stacks 082P] #check (AlgebraicGeometry.AlgebraicSpace.Quot.fpFunctor_isSheaf_fpqc :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent],
      Presheaf.IsSheaf (SchemeOver.fpqcTopology B)
        (AlgebraicGeometry.AlgebraicSpace.Quot.fpFunctor f F))

/- Compatible families of finitely presented kernel-identified quotients of
`F_{T_i}` on an fpqc covering of schemes over `B` glue uniquely to a finitely
presented kernel-identified quotient of `F_T`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Quot.fpFunctor_isSheafFor_fpqcCovering :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
      {ι : Type u} {U : SchemeOver B} {V : ι → SchemeOver B} (h : ∀ i, V i ⟶ U),
      Presieve.ofArrows V h ∈ SchemeOver.fpqcPrecoverage B U →
      Presieve.IsSheafFor (AlgebraicGeometry.AlgebraicSpace.Quot.fpFunctor f F)
        (Presieve.ofArrows V h))

