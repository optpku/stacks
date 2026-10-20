/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Admissible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-!
# Lifting morphisms through isomorphisms over an open subspace

A factorization through an open subspace and an isomorphism over that subspace
determine a lift, including a canonical lift into a fibre product.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical lift of a morphism factoring through `U` along a morphism that is
an isomorphism over `U`. -/
noncomputable def liftAdmissible {S : Scheme.{u}} {W X X' : AlgebraicSpace S}
    (U : OpenSubspace X) (b : X' ⟶ X)
    (hU : W ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b)) : W ⟶ X' :=
  hU ≫ (@inv (AlgebraicSpace S) _ _ _ (pullback.fst U.ι b) hiso) ≫ pullback.snd U.ι b

/-- The admissible lift composes with `b` to the original morphism through `U`. -/
theorem liftAdmissible_fac {S : Scheme.{u}} {W X X' : AlgebraicSpace S}
    (U : OpenSubspace X) (b : X' ⟶ X)
    (hU : W ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b))
    {h : W ⟶ X} (hqU : hU ≫ U.ι = h) :
    liftAdmissible U b hU hiso ≫ b = h :=
  sorry

/-- The two legs defining the lifted morphism to `X' ×_B Y` commute over `B`. -/
theorem liftAdmissiblePullback_condition {S : Scheme.{u}}
    {B X Y V X' : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B)
    (q : V ⟶ pullback f g) (U : OpenSubspace X) (b : X' ⟶ X)
    (qU : V ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b))
    (hqU : qU ≫ U.ι = q ≫ pullback.fst f g) :
    liftAdmissible U b qU hiso ≫ (b ≫ f) = (q ≫ pullback.snd f g) ≫ g :=
  sorry

/-- The morphism `V ⟶ X' ×_B Y` obtained by lifting the first projection of `q`
along a morphism that is an isomorphism over `U`. -/
noncomputable def liftAdmissiblePullback {S : Scheme.{u}}
    {B X Y V X' : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B)
    (q : V ⟶ pullback f g) (U : OpenSubspace X) (b : X' ⟶ X)
    (qU : V ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b))
    (hqU : qU ≫ U.ι = q ≫ pullback.fst f g) :
    V ⟶ pullback (b ≫ f) g :=
  pullback.lift
    (liftAdmissible U b qU hiso)
    (q ≫ pullback.snd f g)
    (liftAdmissiblePullback_condition f g q U b qU hiso hqU)

/-- The first projection of the lifted pullback morphism is the admissible lift. -/
theorem liftAdmissiblePullback_fst {S : Scheme.{u}}
    {B X Y V X' : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B)
    (q : V ⟶ pullback f g) (U : OpenSubspace X) (b : X' ⟶ X)
    (qU : V ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b))
    (hqU : qU ≫ U.ι = q ≫ pullback.fst f g) :
    liftAdmissiblePullback f g q U b qU hiso hqU ≫ pullback.fst (b ≫ f) g =
      liftAdmissible U b qU hiso :=
  sorry

/-- The second projection of the lifted pullback morphism agrees with that of `q`. -/
theorem liftAdmissiblePullback_snd {S : Scheme.{u}}
    {B X Y V X' : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B)
    (q : V ⟶ pullback f g) (U : OpenSubspace X) (b : X' ⟶ X)
    (qU : V ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b))
    (hqU : qU ≫ U.ι = q ≫ pullback.fst f g) :
    liftAdmissiblePullback f g q U b qU hiso hqU ≫ pullback.snd (b ≫ f) g =
      q ≫ pullback.snd f g :=
  sorry

/-- The lifted morphism to `X' ×_B Y` is the unique map induced by the admissible
lift of the first projection and the original second projection. -/
theorem liftAdmissiblePullback_spec {S : Scheme.{u}}
    {B X Y V X' : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B)
    (q : V ⟶ pullback f g) (U : OpenSubspace X) (b : X' ⟶ X)
    (qU : V ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b))
    (hqU : qU ≫ U.ι = q ≫ pullback.fst f g) :
    liftAdmissiblePullback f g q U b qU hiso hqU ≫ pullback.fst (b ≫ f) g =
        liftAdmissible U b qU hiso ∧
      liftAdmissiblePullback f g q U b qU hiso hqU ≫ pullback.snd (b ≫ f) g =
        q ≫ pullback.snd f g :=
  sorry

/-- Quasi-compactness is preserved by the canonical lift to the blown-up fibre
product. -/
theorem quasiCompact_liftAdmissiblePullback {S : Scheme.{u}}
    {B X Y V X' : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B)
    (q : V ⟶ pullback f g) [QuasiCompact q]
    (U : OpenSubspace X) (b : X' ⟶ X)
    (qU : V ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b))
    (hqU : qU ≫ U.ι = q ≫ pullback.fst f g) :
    QuasiCompact (liftAdmissiblePullback f g q U b qU hiso hqU) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
