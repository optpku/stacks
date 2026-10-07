module

public import stacks_project.Chap99.Remark_99_7_3_Descent
public import stacks_project.Chap99.Remark_99_7_3_Quotient

/-!
# Remark 99.7.3

Kernel-identified quasi-coherent quotients of a module on an algebraic space are
in bijection with compatible families of such quotients along an fpqc covering.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.QCoh CategoryTheory.Limits

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

/-- Remark 99.7.3: for a quasi-coherent module `F` on an algebraic space `X`, an
fpqc covering `family` of morphisms `X_i ⟶ X`, and fpqc coverings `overlap i j`
of each fibre product `X_i ×_X X_j`, the restriction map `restrictClass` is a
bijection between kernel-identified quasi-coherent quotients `F ⟶ Q` and
compatible families of quasi-coherent quotients `f_i^* F ⟶ Q_i` that restrict
to the same quotient on each `X_ijk`. -/
@[stacks 08IU]
theorem quotientsRestrict_bijective {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : Type v} {family : I → Over X} (hfamily : FpqcCovering family)
    {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (Limits.pullback (family i).hom (family j).hom))
    (hoverlap : ∀ i j, FpqcCovering (overlap i j))
    (F : X.Modules) [F.IsQuasicoherent] :
    Function.Bijective (restrictClass hfamily overlap hoverlap F) := sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh
