/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import stacks_project.Chap96.Lemma_96_15_1_Abelian
public import stacks_project.Chap103.Definition_103_9_1_Parasitic
public import stacks_project.Chap103.Definition_103_17_2_Coh

/-!
# Coherent modules as a Serre class in quasi-coherent modules

On a locally Noetherian algebraic stack, coherence is a Serre class in
`QCoh(𝒪_X)`. Surjective maps, images, and parasitic kernels transport
coherence along morphisms of quasi-coherent modules.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Limits CategoryTheory.ObjectProperty GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable [AlgebraicStack X] [IsLocallyNoetherian X]

/-- On a locally Noetherian algebraic stack, the quasi-coherent modules that are
coherent form a Serre class in `QCoh(𝒪_X)`. -/
instance Coh.isSerreClass :
    ((coherentModuleProperty X).inverseImage (QCoh.inclusion X)).IsSerreClass :=
  sorry

/-- A quasi-coherent `𝒪_X`-module lies in the inverse image of coherence along
`QCoh.inclusion` if and only if its underlying module sheaf is coherent. -/
theorem mem_inverseImage_inclusion_iff (F : QCoh X) :
    (coherentModuleProperty X).inverseImage (QCoh.inclusion X) F ↔
      AlgebraicStack.IsCoherent F.obj :=
  sorry

/-- A surjective map of quasi-coherent `𝒪_X`-modules with coherent source has
coherent target. -/
theorem isCoherent_of_epi {F G : QCoh X} (φ : F ⟶ G) [Epi φ]
    [AlgebraicStack.IsCoherent F.obj] :
    AlgebraicStack.IsCoherent G.obj :=
  sorry

/-- The image in `Mod(𝒪_X)` of a map of quasi-coherent `𝒪_X`-modules with
coherent source is coherent. -/
instance isCoherent_image_of_qCohHom {F G : QCoh X} (φ : F ⟶ G)
    [AlgebraicStack.IsCoherent F.obj] :
    AlgebraicStack.IsCoherent (Abelian.image ((QCoh.inclusion X).map φ)) :=
  sorry

/-- A map of quasi-coherent `𝒪_X`-modules with coherent target and parasitic
kernel, computed in `Mod(𝒪_X)`, has coherent source. -/
theorem isCoherent_of_isParasitic_kernel {F G : QCoh X} (φ : F ⟶ G)
    [AlgebraicStack.IsCoherent G.obj]
    [IsParasitic (kernel ((QCoh.inclusion X).map φ)).val] :
    AlgebraicStack.IsCoherent F.obj :=
  sorry

end AlgebraicGeometry.AlgebraicStack
