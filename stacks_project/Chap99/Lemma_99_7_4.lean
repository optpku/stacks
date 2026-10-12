/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap77.Lemma_77_7_2_FpqcTopology
public import stacks_project.Chap99.«99_7_1_1_Functor»
public import stacks_project.Chap99.«99_7_1_2_Functor»

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- Lemma 99.7.4 (1): in Situation 99.7.1 the functor `Q_{F/X/B}` on `(Sch/B)ᵒᵖ`
satisfies the sheaf property for the fpqc topology. -/
@[stacks 082P]
theorem functor_isSheaf_fpqc {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology B) (functor f F) :=
  sorry

/-- Compatible families of kernel-identified quotients of `F_{T_i}` on an fpqc
covering of schemes over `B` glue uniquely to a kernel-identified quotient of
`F_T`. -/
theorem functor_isSheafFor_fpqcCovering {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {ι : Type u} {U : SchemeOver B} {V : ι → SchemeOver B} (h : ∀ i, V i ⟶ U)
    (h_cover : Presieve.ofArrows V h ∈ SchemeOver.fpqcPrecoverage B U) :
    Presieve.IsSheafFor (functor f F) (Presieve.ofArrows V h) :=
  sorry

/-- Lemma 99.7.4 (2): in Situation 99.7.1 the functor `Q^{fp}_{F/X/B}` on
`(Sch/B)ᵒᵖ` satisfies the sheaf property for the fpqc topology. -/
@[stacks 082P]
theorem fpFunctor_isSheaf_fpqc {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology B) (fpFunctor f F) :=
  sorry

/-- Compatible families of finitely presented kernel-identified quotients of
`F_{T_i}` on an fpqc covering of schemes over `B` glue uniquely to a finitely
presented kernel-identified quotient of `F_T`. -/
theorem fpFunctor_isSheafFor_fpqcCovering {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {ι : Type u} {U : SchemeOver B} {V : ι → SchemeOver B} (h : ∀ i, V i ⟶ U)
    (h_cover : Presieve.ofArrows V h ∈ SchemeOver.fpqcPrecoverage B U) :
    Presieve.IsSheafFor (fpFunctor f F) (Presieve.ofArrows V h) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
