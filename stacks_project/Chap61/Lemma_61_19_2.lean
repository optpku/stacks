/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleFullyFaithful
import StacksCheckRecall

/-!
# Lemma 61.19.2

The adjunction unit of `ε⁻¹ ⊣ ε_*` along `etaleToProEt` is an isomorphism on
every sheaf of sets on `X.Etale`.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})
variable [∀ P : X.Etaleᵒᵖ ⥤ Type (u + 1), (etaleToProEt X).op.HasLeftKanExtension P]
variable [HasWeakSheafify (ProEt.topology X) (Type (u + 1))]

/- Lemma 61.19.2: for a scheme `X` and every sheaf of sets `F` on `X.Etale`,
the adjunction map `F ⟶ ε_* ε⁻¹ F` is an isomorphism, i.e.,
`ε⁻¹ F` evaluated at `u(U)` agrees with `F(U)` for `U` in `X.Etale`. -/
@[stacks 099T] #check (AlgebraicGeometry.Scheme.EtaleToProEt.unit_app_isIso X :
  ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1))),
    IsIso ((etaleToProEt_sheafAdjunction X (Type (u + 1))).unit.app F))

/-- The comparison morphism `F(U) ⟶ ε⁻¹ F(u(U))` obtained by composing the
adjunction unit with restriction of `ε_*` along `etaleToProEt`. -/
def etaleToProEtPullback_obj_etale
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale) :
    F.obj.obj (op U) ⟶
      (((etaleToProEtPullback X (Type (u + 1))).obj F).obj.obj
        (op ((etaleToProEt X).obj U))) :=
  EtaleToProEt.obj_etale X F U

/-- The comparison morphism `F(U) ⟶ ε⁻¹ F(u(U))` is an isomorphism. -/
instance etaleToProEtPullback_obj_etale_isIso
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (U : X.Etale) :
    IsIso (etaleToProEtPullback_obj_etale X F U) :=
  EtaleToProEt.obj_etale_isIso X F U

end AlgebraicGeometry.Scheme
