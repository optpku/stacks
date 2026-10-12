/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.EtaleCohomology.SetCechDescent
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open scoped Simplicial

universe u

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [IsFinite f] [Surjective f] [(Arrow.mk f).HasCechNerve]
variable [HasWeakSheafify Y.smallEtaleTopology (Type u)]
variable [∀ n : ℕ, HasWeakSheafify (finiteCechScheme f n).smallEtaleTopology (Type u)]
variable [∀ P : Y.Etaleᵒᵖ ⥤ Type u, ∀ n : ℕ,
  (smallEtalePullback (finiteCechMap f n)).op.HasLeftKanExtension P]
variable [∀ n m : ℕ, ∀ P : (finiteCechScheme f n).Etaleᵒᵖ ⥤ Type u,
  ∀ α : ⦋n⦌ ⟶ ⦋m⦌,
    (smallEtalePullback (finiteCechNerve_map f α)).op.HasLeftKanExtension P]
variable (G : Sheaf Y.smallEtaleTopology (Type u))

/- Remark 59.55.6 (1): a sheaf of sets `G` on `Y_étale` is the equalizer of
`f_{0,*} f_0^{-1} G ⇉ f_{1,*} f_1^{-1} G`. -/
@[stacks 09Z3] #check (AlgebraicGeometry.Scheme.Etale.finiteCech_setSheaf_isEqualizer f G :
  IsEqualizer (finiteCechSet_unit f G 0)
    (finiteCechSetSheaf_face f G 0) (finiteCechSetSheaf_face f G 1)
    (finiteCechSetSheaf_face_equalizes f G))

/- Remark 59.55.6 (2): `Γ(Y, G)` is the equalizer of
`Γ(X_0, f_0^{-1} G) ⇉ Γ(X_1, f_1^{-1} G)`. -/
@[stacks 09Z3] #check
  (AlgebraicGeometry.Scheme.Etale.finiteCech_setSheaf_globalSections_equalizer f G :
    IsEqualizer (TypeCat.ofHom (etaleSectionsPullback (finiteCechMap f 0) G))
      (finiteCechSet_invImage_face f G 0) (finiteCechSet_invImage_face f G 1)
      (finiteCechSet_invImage_face_equalizes f G))

end
