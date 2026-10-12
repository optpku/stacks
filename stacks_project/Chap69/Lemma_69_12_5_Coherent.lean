/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal

/-!
# Tensor and internal Hom of coherent modules on locally Noetherian algebraic spaces

On a locally Noetherian algebraic space, coherent `𝒪_X`-modules are closed under tensor product
and internal Hom.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
variable {F G : X.Modules}

/-- The tensor product of coherent modules on a locally Noetherian algebraic space is
coherent. -/
@[instance]
theorem isCoherent_tensor [F.IsCoherent] [G.IsCoherent] : (F ⊗ G).IsCoherent :=
  sorry

/-- The internal Hom of coherent modules on a locally Noetherian algebraic space is
coherent. -/
@[instance]
theorem isCoherent_internalHom [F.IsCoherent] [G.IsCoherent] :
    (internalHom F G).IsCoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
