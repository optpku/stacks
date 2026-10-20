module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import stacks_project.Chap71.Lemma_71_16_1_Kernel
public import stacks_project.Chap71.Lemma_71_16_1_Quotient

/-!
# Lemma 71.16.1

A quasi-compact closed subspace of relative Proj of a quasi-coherent graded
algebra is itself relative Proj of the quotient by the kernel of the canonical
map to the pushed-forward restricted twists.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

/-- Lemma 71.16.1
Let `S` be a scheme, `X` an algebraic space over `S`, and `𝒜` a quasi-coherent
graded `𝒪_X`-algebra. Let `π : P = underline{Proj}_X(𝒜) ⟶ X` be the relative
Proj of `𝒜`, and let `i : Z ⟶ P` be a closed subspace. Denote `I ⊂ 𝒜` the
kernel of the canonical map `𝒜 ⟶ ⊕_{d ≥ 0} π_* ((i_* 𝒪_Z)(d))`. If `π` is
quasi-compact, then there is an isomorphism `Z = underline{Proj}_X(𝒜 / I)`. -/
@[stacks 085L]
theorem existsClosedSubspaceQuotient
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] [hqc : 𝒜.IsQuasicoherent]
    {deg : DegreePieces 𝒜} (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) {Z : AlgebraicSpace S}
    (i : Z ⟶ toAlgebraicSpace F hF)
    [IsClosedImmersion i] [QuasiCompact (toAlgebraicSpace_hom F hF)] :
    Nonempty (CanonicalClosedSubspaceQuotient F hF i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
