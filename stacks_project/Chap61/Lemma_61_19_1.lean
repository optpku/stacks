/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtalePullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open scoped MorphismOfTopoiIn

universe u

variable {X : Scheme.{u}}
variable [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology (Type (u + 1))]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z),
  ∀ P : Z.Etaleᵒᵖ ⥤ Type (u + 1),
    (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ Type (u + 1),
  (etaleToProEt X).op.HasLeftKanExtension P]
variable [HasWeakSheafify (ProEt.topology X) (Type (u + 1))]

/- Lemma 61.19.1 (1): global sections of small étale inverse images form a
sheaf on the small pro-étale site. -/
@[stacks 0GLZ] #check (AlgebraicGeometry.Scheme.etalePullbackGamma_isSheaf :
  ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1))),
    Presheaf.IsSheaf (ProEt.topology X) (etalePullbackGamma F))

/- Lemma 61.19.1 (2): the formula sheaf is isomorphic to comparison inverse
image. -/
@[stacks 0GLZ] #check (AlgebraicGeometry.Scheme.etalePullbackGammaSheaf_iso :
  ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1))),
    IsIsomorphic (etalePullbackGammaSheaf F)
      ((etaleToProEtPullback X (Type (u + 1))).obj F))

variable {Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
variable (F : Sheaf X.smallEtaleTopology (Type (u + 1)))

#check (AlgebraicGeometry.Scheme.etaleToProEtPullback_obj_obj X F (ProEt.mk f) :
  IsIsomorphic
    (((etaleToProEtPullback X (Type (u + 1))).obj F).obj.obj (op (ProEt.mk f)))
    ((((smallMorphism f)⁻¹).obj F).obj.obj (op (Etale.globalEtale Y))))
