/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleSectionsComparison
import StacksCheckRecall

/-!
# Lemma 61.19.3

Sections of `ε⁻¹ F` on a directed inverse limit of qcqs objects of
`X.ProEt` with affine transitions commute with the filtered colimit of
stage sections.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {X : Scheme.{u}}
variable [∀ P : X.Etaleᵒᵖ ⥤ Type (u + 1), (etaleToProEt X).op.HasLeftKanExtension P]
variable [HasWeakSheafify (ProEt.topology X) (Type (u + 1))]

section proEtStages

variable (D : OrderDual I ⥤ X.ProEt)
variable [∀ {i j : I} (hij : i ≤ j),
    IsAffineHom (OrderDualInverseSystem.transitionMap D hij).left]
variable [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i)).left]
variable [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i)).left]
variable (c : Cone D)
variable (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
variable [HasColimit (etaleToProEtPullbackSectionsDiagram D F)]

/- Lemma 61.19.3 (1): for a scheme `X` and a directed inverse system of
quasi-compact and quasi-separated objects of `X.ProEt` with affine transition
morphisms, every sheaf of sets `F` on `X.Etale` satisfies
`ε⁻¹ F(Y) = colim ε⁻¹ F(Y_i)`, as an isomorphism of the canonical comparison
from the colimit of stage sections. -/
@[stacks 099S] #check (AlgebraicGeometry.Scheme.etaleToProEtPullback_sectionsColimit D c F :
  IsLimit ((ProEt.forget X ⋙ Over.forget X).mapCone c) →
    IsIso (etaleToProEtPullbackSectionsComparison D c F))

end proEtStages

section etaleStages

variable (E : OrderDual I ⥤ X.Etale)
variable [∀ {i j : I} (hij : i ≤ j),
    IsAffineHom (OrderDualInverseSystem.transitionMap (E ⋙ etaleToProEt X) hij).left]
variable [∀ i : I, CompactSpace ((E ⋙ etaleToProEt X).obj (OrderDual.toDual i)).left]
variable [∀ i : I, QuasiSeparatedSpace ((E ⋙ etaleToProEt X).obj (OrderDual.toDual i)).left]
variable (c : Cone (E ⋙ etaleToProEt X))
variable (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
variable [HasColimit (etaleToProEtPullbackEtaleSectionsDiagram E F)]

/- Lemma 61.19.3 (2): if in addition the stages `Y_i` lie in `X.Etale`, then
`ε⁻¹ F(Y) = colim F(Y_i)`. -/
@[stacks 099S] #check (AlgebraicGeometry.Scheme.etaleToProEtPullback_etaleSectionsColimit E c F :
  IsLimit ((ProEt.forget X ⋙ Over.forget X).mapCone c) →
    IsIso (etaleToProEtPullbackEtaleSectionsComparison E c F))

end etaleStages

end AlgebraicGeometry.Scheme
