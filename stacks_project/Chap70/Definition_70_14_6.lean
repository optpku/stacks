/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_14_5_SectionsWithSupport
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X U : AlgebraicSpace S}
variable (ι : U ⟶ X) [IsOpenImmersion ι] (F : X.Modules)

/- Definition 70.14.6: let `S` be a scheme and `X` an algebraic space over `S`.
If `T ⊂ |X|` is a closed subset whose complement corresponds to an open subspace
`U ⊂ X` with quasi-compact inclusion `U ⟶ X`, and `F` is a quasi-coherent
`𝒪_X`-module, then the quasi-coherent subsheaf `sectionsWithSupportIn ι F ⊂ F`
constructed in Lemma 70.14.5 is called the subsheaf of sections supported on `T`.
Here `T` is the closed complement of the image of `Points.map ι`. -/
@[stacks 085A]
#check (sectionsWithSupportIn ι F : X.Modules)

/- The named subsheaf includes canonically into `F`. -/
#check (sectionsWithSupportInι ι F : sectionsWithSupportIn ι F ⟶ F)

/- If `U ⟶ X` is quasi-compact and `F` is quasi-coherent, then the subsheaf of
sections supported on `T` is quasi-coherent. -/
variable [QuasiCompact ι] [F.IsQuasicoherent] in
#check (sectionsWithSupportIn_isQuasicoherent ι F :
  (sectionsWithSupportIn ι F).IsQuasicoherent)

end AlgebraicGeometry.AlgebraicSpace.Modules
