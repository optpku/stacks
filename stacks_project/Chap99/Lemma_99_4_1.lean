/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap77.Lemma_77_7_2_FpqcTopology
public import stacks_project.Chap99.Lemma_99_4_1_Functor

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 99.4.1: in Situation 99.3.1 the functor `Isom(F, G)` on `(Sch/B)ᵒᵖ`
satisfies the sheaf property for the fpqc topology. -/
@[stacks 08K8]
theorem isomFunctor_isSheaf_fpqc {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology B) (isomFunctor f F G) :=
  sorry

/-- Compatible families of isomorphisms `F_{T_i} ⟶ G_{T_i}` on an fpqc covering of
schemes over `B` glue uniquely to an isomorphism `F_T ⟶ G_T`. -/
theorem isomFunctor_isSheafFor_fpqcCovering {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {ι : Type u} {U : SchemeOver B} {V : ι → SchemeOver B} (h : ∀ i, V i ⟶ U)
    (h_cover : Presieve.ofArrows V h ∈ SchemeOver.fpqcPrecoverage B U) :
    Presieve.IsSheafFor (isomFunctor f F G) (Presieve.ofArrows V h) :=
  sorry

/-- An `𝒪_{X_T}`-module map whose restrictions along an fpqc covering of schemes
over `B` are isomorphisms is itself an isomorphism. -/
theorem isIso_of_fpqcCovering {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {ι : Type u} {U : SchemeOver B} {V : ι → SchemeOver B} (h : ∀ i, V i ⟶ U)
    (h_cover : Presieve.ofArrows V h ∈ SchemeOver.fpqcPrecoverage B U)
    (u : baseChangeModule f U.hom F ⟶ baseChangeModule f U.hom G)
    (h_iso : ∀ i, IsIso (baseChangeHom f F G (h i) u)) : IsIso u :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
