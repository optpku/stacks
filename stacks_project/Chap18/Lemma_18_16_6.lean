/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.LowerShriek
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousLeftAdjoint
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint
import StacksCheckRecall

/-!
# Lemma 18.16.6

Lower shriek along a continuous right adjoint is exact and agrees on underlying sheaves with the
set-valued lower shriek; a cocontinuous left adjoint identifies it with inverse image.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
variable [u.IsRightAdjoint]

section Underlying

variable [HasWeakSheafify K AddCommGrpCat.{w}]
variable [HasWeakSheafify K (Type w)]
variable [J.HasSheafCompose (forget AddCommGrpCat.{w})]
variable [K.HasSheafCompose (forget AddCommGrpCat.{w})]
variable [(forget AddCommGrpCat.{w}).PreservesLeftKanExtensions u.op]
variable [K.PreservesSheafification (forget AddCommGrpCat.{w})]

/- Lemma 18.16.6 (1a) (08P3): abelian and set-valued lower shriek agree after forgetting the
abelian-group structure. -/
@[stacks 08P3 "(1), underlying sheaves"]
#check (Functor.AbelianLowerShriek.underlyingIso_of_isRightAdjoint u :
  u.sheafPullback AddCommGrpCat.{w} J K ⋙
      sheafCompose K (forget AddCommGrpCat.{w}) ≅
    sheafCompose J (forget AddCommGrpCat.{w}) ⋙
      u.sheafPullback (Type w) J K)

end Underlying

section Exact

variable [HasSheafify K AddCommGrpCat.{w}]

/- Lemma 18.16.6 (1b) (08P3): abelian lower shriek is exact. -/
@[stacks 08P3 "(1), exactness"]
#check (Functor.AbelianLowerShriek.exact_of_isRightAdjoint u :
  exactFunctor
    (Sheaf J AddCommGrpCat.{w}) (Sheaf K AddCommGrpCat.{w})
      (u.sheafPullback AddCommGrpCat.{w} J K))

end Exact

section Adjunction

variable (w : D ⥤ C) (adj : w ⊣ u) [w.IsCocontinuous K J]
variable [HasWeakSheafify K AddCommGrpCat.{w}]

/- Lemma 18.16.6 (2a) (08P3): abelian lower shriek along `u` is inverse image along `w`. -/
@[stacks 08P3 "(2), lower shriek"]
#check (Functor.LeftAdjoint.pullbackIsoCocontinuous
  u w adj AddCommGrpCat.{w} :
    u.sheafPullback AddCommGrpCat.{w} J K ≅
      w.sheafPullbackCocontinuous AddCommGrpCat.{w} K J)

variable [∀ P : Dᵒᵖ ⥤ Type w, w.op.HasPointwiseRightKanExtension P]

/- Lemma 18.16.6 (2b) (08P3): inverse image along `u` is direct image along `w`. -/
@[stacks 08P3 "(2), inverse image"]
#check (Functor.ContinuousRightAdjoint.pushforwardContinuousIso
  w u (Type w) adj :
    u.sheafPushforwardContinuous (Type w) J K ≅
      w.sheafPushforwardCocontinuous (Type w) K J)

end Adjunction

end CategoryTheory
