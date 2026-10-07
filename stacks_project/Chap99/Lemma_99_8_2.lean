module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap77.Lemma_77_7_2_FpqcTopology
public import stacks_project.Chap99.«99_8_1_1_Functor»

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- Lemma 99.8.2: in Situation 99.8.1 the functor `Quot_{F/X/B}` on `(Sch/B)ᵒᵖ`
satisfies the sheaf property for the fpqc topology. -/
@[stacks 09TT]
theorem quot_isSheaf_fpqc {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [FinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology B) (quot f F) :=
  sorry

/-- Compatible families of kernel-identified Quot-points of `F_{T_i}` on an
fpqc covering of schemes over `B` glue uniquely to a kernel-identified
Quot-point of `F_T`. -/
theorem quot_isSheafFor_fpqcCovering {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [FinitePresentation f] (F : X.Modules) [F.IsQuasicoherent]
    {ι : Type u} {U : SchemeOver B} {V : ι → SchemeOver B} (h : ∀ i, V i ⟶ U)
    (h_cover : Presieve.ofArrows V h ∈ SchemeOver.fpqcPrecoverage B U) :
    Presieve.IsSheafFor (quot f F) (Presieve.ofArrows V h) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
